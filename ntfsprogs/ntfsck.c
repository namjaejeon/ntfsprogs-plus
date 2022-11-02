/**
 * ntfsck - Part of the Linux-NTFS project.
 *
 * Copyright (c) 2006 Yuval Fledel
 *
 * This utility will check and fix errors on an NTFS volume.
 *
 * This program is free software; you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as published by
 * the Free Software Foundation; either version 2 of the License, or
 * (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program (in the main directory of the Linux-NTFS
 * distribution in the file COPYING); if not, write to the Free Software
 * Foundation,Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA
 */


#include "config.h"

#ifdef HAVE_STDIO_H
#include <stdio.h>
#endif
#ifdef HAVE_STDLIB_H
#include <stdlib.h>
#endif
#ifdef HAVE_STRING_H
#include <string.h>
#endif
#ifdef HAVE_FCNTL_H
#include <fcntl.h>
#endif

#include <layout.h>
#include <bitmap.h>
#include <endians.h>
#include <bootsect.h>
#include <misc.h>
#include <getopt.h>

#include "cluster.h"
#include "utils.h"
#include "list.h"
#include "dir.h"

#define RETURN_FS_ERRORS_CORRECTED (1)
#define RETURN_SYSTEM_NEEDS_REBOOT (2)
#define RETURN_FS_ERRORS_LEFT_UNCORRECTED (4)
#define RETURN_OPERATIONAL_ERROR (8)
#define RETURN_USAGE_OR_SYNTAX_ERROR (16)
#define RETURN_CANCELLED_BY_USER (32)
/* Where did 64 go? */
#define RETURN_SHARED_LIBRARY_ERROR (128)

/* todo: command line: (everything is optional)
 *  fsck-frontend options:
 *	-C [fd]	: display progress bar (send it to the file descriptor if specified)
 *	-T	: don't show the title on startup
 *  fsck-checker options:
 *	-a	: auto-repair. no questions. (optional: if marked clean and -f not specified, just check if mounable)
 *	-p	: auto-repair safe. no questions (optional: same)
 *	-n	: only check. no repair.
 *	-r	: interactively repair.
 *	-y	: always yes.
 *	-v	: verbose.
 *	-V	: version.
 *  taken from fsck.ext2
 *	-b sb	: use the superblock from sb. For corrupted volumes. (do we want separete boot/mft options?)
 *	-c	: use badblocks(8) to find bad blocks (R/O mode) and add the findings to $Bad.
 *	-C fd	: write competion info to fd. If 0, print a completion bar.
 *	-d	: debugging output.
 *	-D	: rebalance indices.
 *	-f	: force checking even if marked clean.
 *	-F	: flush buffers before beginning. (for time-benchmarking)
 *	-k	: When used with -c, don't erase previous $Bad items.
 *	-n	: Open fs as readonly. assume always no. (why is it needed if -r is not specified?)
 *	-t	: Print time statistics.
 *  taken from fsck.reiserfs
 *	--rebuild-sb	: try to find $MFT start and rebuild the boot sector.
 *	--rebuild-tree	: scan for items and rebuild the indices that point to them (0x30, $SDS, etc.)
 *	--clean-reserved: zero rezerved fields. (use with care!)
 *	--adjust-size -z: insert a sparse hole if the data_size is larger than the size marked in the runlist.
 *	--logfile file	: report corruptions (unlike other errors) to a file instead of stderr.
 *	--nolog		: don't report corruptions at all.
 *	--quiet -q	: no progress bar.
 *  taken from fsck.msdos
 *	-w	: flush after every write.
 *	- do n passes. (only 2 in fsck.msdos. second should not report errors. Bonus: stop when error list does not change)
 *  taken from fsck.jfs
 *	--omit-journal-reply: self-descriptive (why would someone do that?)
 *	--replay-journal-only: self-descriptive. don't check otherwise.
 *  taken from fsck.xfs
 *	-s	: only serious errors should be reported.
 *	-i ino	: verbose behaviour only for inode ino.
 *	-b bno	: verbose behaviour only for cluster bno.
 *	-L	: zero log.
 *  inspired by others
 *	- don't do cluster accounting.
 *	- don't do mft record accounting.
 *	- don't do file names accounting.
 *	- don't do security_id accounting.
 *	- don't check acl inheritance problems.
 *	- undelete unused mft records. (bonus: different options for 100% salvagable and less)
 *	- error-level-report n: only report errors above this error level
 *	- error-level-repair n: only repair errors below this error level
 *	- don't fail on ntfsclone metadata pruning.
 *  signals:
 *	SIGUSR1	: start displaying progress bar
 *	SIGUSR2	: stop displaying progress bar.
 */

static struct {
	int verbose;
	ntfs_mount_flags flags;
} option;

int parse_count = 1;

/**
 * usage
 */
__attribute__((noreturn))
static void usage(int ret)
{
	ntfs_log_info("ntfsck v%s (libntfs-3g)\n\n"
		      "Usage: ntfsck [options] device\n"
		      "-a, --repair-auto	auto-repair. no questions\n"
		      "-p,			auto-repair. no questions\n"
		      "-n, --repair-no		just check the consistency and no fix\n"
		      "-r, --repair		Repair interactively\n"
		      "-y, --repair-yes		all yes about all question\n"
		      "-v, --verbose		verbose\n"
		      "-V, --version		version\n\n"
		      "For example: ntfsck /dev/sda1\n\n", VERSION);
	exit(ret);
}

/**
 * version
 */
__attribute__((noreturn))
static void version(void)
{
	ntfs_log_info("ntfsck v%s\n\n", VERSION);
	ntfs_log_info("%s\n%s%s", ntfs_gpl, ntfs_bugs, ntfs_home);
	exit(0);
}

static const struct option opts[] = {
	{"repair-auto",		no_argument,		NULL,	'a' },
	{"repair-no",		no_argument,		NULL,	'n' },
	{"repair",		no_argument,		NULL,	'r' },
	{"repair-yes",		no_argument,		NULL,	'y' },
	{"verbose",		no_argument,		NULL,	'v' },
	{"version",		no_argument,		NULL,	'V' },
	{NULL,			0,			NULL,	 0  }
};

ntfschar NTFS_INDEX_I30[5] = { const_cpu_to_le16('$'), const_cpu_to_le16('I'),
	const_cpu_to_le16('3'), const_cpu_to_le16('0'),
	const_cpu_to_le16('\0') };

static u8 *fsck_mft_bmp;
static s64 fsck_mft_bmp_size;

u8 *fsck_lcn_bitmap;
unsigned int fsck_lcn_bitmap_size;

static void ntfsck_check_orphaned_clusters(ntfs_volume *vol)
{
	s64 pos = 0, wpos, i, count, written;
	BOOL backup_boot_sec_bit = FALSE, repair = FALSE;
	u8 bm[NTFS_BUF_SIZE];

	ntfs_log_info("Parse #%d: Check cluster bitmap...\n", parse_count++);

	while (1) {
		wpos = pos;
		count = ntfs_attr_pread(vol->lcnbmp_na, pos, NTFS_BUF_SIZE, bm);
		if (count == -1) {
			ntfs_log_error("Couldn't get $Bitmap $DATA");
			break;
		}

		if (count == 0) {
			/* the backup bootsector need not be accounted for */
			if (((vol->nr_clusters + 7) >> 3) > pos)
				ntfs_log_error("$Bitmap size is smaller than expected (%lld < %lld)\n",
						(long long)pos, (long long)vol->lcnbmp_na->data_size);
			break;
		}

		for (i = 0; i < count; i++, pos++) {
			s64 cl;  /* current cluster */

			if (pos > fsck_lcn_bitmap_size)
				continue;

			if (fsck_lcn_bitmap[pos] == bm[i])
				continue;

			for (cl = pos * 8; cl < (pos + 1) * 8; cl++) {
				char lbmp_bit, fsck_bmp_bit;

				/*
				 * Don't count cluster allocation bit for backup
				 * boot sector. Too much allocation bitmap for
				 * this bit is not need to be allocated.
				 */
				if (cl == vol->nr_clusters) {
					backup_boot_sec_bit = TRUE;
					continue;
				}

				if (cl > vol->nr_clusters)
					break;

				lbmp_bit = ntfs_bit_get(bm, i * 8 + cl % 8);
				fsck_bmp_bit = ntfs_bit_get(fsck_lcn_bitmap, cl);
				if (fsck_bmp_bit != lbmp_bit) {
					if (fsck_bmp_bit == 0 && lbmp_bit == 1) {
						check_failed("Found orphaned cluster bit : %ld. Clear orphaned cluster bit in cluster bitmap", cl);
					} else {
						check_failed("Found missing cluster bit set : %ld in cluster bitmap. Set orphaned cluster bit into cluster bitmap", cl);
					}
					if (ntfsck_ask_repair(vol)) {
						ntfs_bit_set(bm, i * 8 + cl % 8, !lbmp_bit);
						repair = TRUE;
						errors--;
					}
				}
			}
		}

		if (repair == TRUE) {
			written = ntfs_attr_pwrite(vol->lcnbmp_na, wpos, count, bm);
			if (written != count)
				ntfs_log_error("lcn bitmap write failed, pos : %ld, count : %ld, written : %ld\n",
					wpos, count, written);
			repair = FALSE;
		}
	}

	if (backup_boot_sec_bit == FALSE)
		ntfs_log_error("Last cluster bit for backup boot sector is not set in $Bitmap\n");
}

static void ntfsck_set_bitmap_range(u8 *bm, s64 pos, s64 length, u8 bit)
{
	while (length--)
		ntfs_bit_set(bm, pos++, bit);
}

static int ntfsck_update_lcn_bitmap(ntfs_inode *ni)
{
	ntfs_attr_search_ctx *actx;

	actx = ntfs_attr_get_search_ctx(ni, NULL);
	if (!actx)
		return -ENOMEM;

	while (!ntfs_attrs_walk(actx)) {
		runlist *rl;
		int i = 0;

		if (!actx->attr->non_resident)
			continue;

		rl = ntfs_mapping_pairs_decompress(ni->vol, actx->attr,
				NULL);
		if (!rl) {
			ntfs_log_error("Failed to decompress runlist.  Leaving inconsistent metadata.\n");
			continue;
		}

		while (rl[i].length) {
			if (rl[i].lcn > (LCN)LCN_HOLE) {
				if (fsck_lcn_bitmap_size <
				    (rl[i].lcn + 1 + rl[i].length) >> 3) {
					int off = fsck_lcn_bitmap_size;

					fsck_lcn_bitmap_size +=
						((rl[i].lcn + 1 + rl[i].length +
						  (NTFS_BLOCK_SIZE - 1)) &
						 ~(NTFS_BLOCK_SIZE - 1)) >> 3;
					fsck_lcn_bitmap = ntfs_realloc(fsck_lcn_bitmap,
							fsck_lcn_bitmap_size);
					memset(fsck_lcn_bitmap + off, 0,
							fsck_lcn_bitmap_size - off);
				}
				ntfs_log_verbose("Cluster run of mft entry(%ld) : lcn : %ld, length : %ld\n",
						ni->mft_no, rl[i].lcn, rl[i].length);

				ntfsck_set_bitmap_range(fsck_lcn_bitmap,
						rl[i].lcn, rl[i].length, 1);
			}
			++i;
		}

		free(rl);
	}

	return 0;
}

static void ntfsck_verify_mft_record(ntfs_volume *vol, s64 mft_num)
{
	int is_used;
	int always_exist_sys_meta_num = vol->major_ver >= 3 ? 11 : 10;
	ntfs_inode *ni;

	is_used = utils_mftrec_in_use(vol, mft_num);
	if (is_used < 0) {
		ntfs_log_error("Error getting bit value for record %lld.\n",
			(long long)mft_num);
		errors++;
		return;
	} else if (!is_used) {
		if (mft_num <= always_exist_sys_meta_num) {
			ntfs_log_verbose("Record %lld unused. Fixing or fail about system files.\n",
					(long long)mft_num);
			errors++;
			return;
		}

		ntfs_log_verbose("Record %lld unused. Skipping.\n",
				(long long)mft_num);
		return;
	}

	ntfs_log_verbose("MFT record %lld\n", (long long)mft_num);

	ni = ntfs_inode_open(vol, mft_num);
	if (!ni) {
		check_failed("Clear the bit of mft no(%ld) in the $MFT/$BITMAP corresponding orphaned MFT record",
				mft_num);
		if (ntfsck_ask_repair(vol)) {
			if (ntfs_bitmap_clear_bit(vol->mftbmp_na, mft_num)) {
				ntfs_log_error("ntfs_bitmap_clear_bit failed, errno : %d\n",
						errno);
				return;
			}
			errors--;
		}
		return;
	}

	is_used = ntfs_bit_get(fsck_mft_bmp, mft_num);
	if (!is_used) {
		check_failed("Found an orphaned file(mft no: %ld). Fix",
				mft_num);
		if (ntfsck_ask_repair(vol)) {
			/* FIXME: Should we remove each attributes here in mft entry ? */

			while (ni->nr_extents)
				if (ntfs_mft_record_free(vol, *(ni->extent_nis))) {
					ntfs_log_error("Failed to free extent MFT record.  "
							"Leaving inconsistent metadata.\n");
				}
			if (ntfs_mft_record_free(vol, ni))
				ntfs_log_error("Failed to free MFT record.  "
						"Leaving inconsistent metadata. Run chkdsk.\n");
			errors--;
			return;
		}
	}

	/*
	 * Update number of clusters that is used for each non-resident mft entries to
	 * bitmap.
	 */
	ntfsck_update_lcn_bitmap(ni);

	ntfs_inode_close(ni);
}

#if DEBUG
void ntfsck_debug_print_fn_attr(ntfs_attr_search_ctx *actx,
		FILE_NAME_ATTR *idx_fn, FILE_NAME_ATTR *mft_fn)
{
	STANDARD_INFORMATION *std_info;
	ntfs_time si_ctime;
	ntfs_time si_mtime;
	ntfs_time si_mtime_mft;
	ntfs_time si_atime;
	ntfs_inode *ni;
	BOOL diff = FALSE;

	if (!actx)
		return;

	if (ntfs_attr_lookup(AT_STANDARD_INFORMATION, AT_UNNAMED,
				0, CASE_SENSITIVE, 0, NULL, 0, actx)) {
		/* it's not possible here, because $STD_INFO's already checked
		 * in ntfs_inode_open() */
		return;
	}

	ni = actx->ntfs_ino;

	std_info = (STANDARD_INFORMATION *)((u8 *)actx->attr +
			le16_to_cpu(actx->attr->value_offset));
	si_ctime = std_info->creation_time;
	si_mtime = std_info->last_data_change_time;
	si_mtime_mft = std_info->last_mft_change_time;
	si_atime = std_info->last_access_time;

	if (si_mtime != mft_fn->last_data_change_time ||
			si_mtime_mft != mft_fn->last_mft_change_time) {
		ntfs_log_debug("STD TIME != MFT/$FN\n");
		diff = TRUE;
	}

	if (si_mtime != ni->last_data_change_time ||
			si_mtime_mft != ni->last_mft_change_time) {
		ntfs_log_debug("STD TIME != INODE\n");
		diff = TRUE;
	}

	if (si_mtime != idx_fn->last_data_change_time ||
			si_mtime_mft != idx_fn->last_mft_change_time) {
		ntfs_log_debug("STD TIME != IDX/$FN\n");
		diff = TRUE;
	}

	if (idx_fn->parent_directory != mft_fn->parent_directory) {
		ntfs_log_debug("different parent_directory IDX/$FN, MFT/$FN\n");
		diff = TRUE;
	}
	if (idx_fn->allocated_size != mft_fn->allocated_size) {
		ntfs_log_debug("different allocated_size IDX/$FN, MFT/$FN\n");
		diff = TRUE;
	}
	if (idx_fn->allocated_size != mft_fn->allocated_size) {
		ntfs_log_debug("different allocated_size IDX/$FN, MFT/$FN\n");
		diff = TRUE;
	}
	if (idx_fn->data_size != mft_fn->data_size) {
		ntfs_log_debug("different data_size IDX/$FN, MFT/$FN\n");
		diff = TRUE;
	}

	if (idx_fn->reparse_point_tag != mft_fn->reparse_point_tag) {
		ntfs_log_debug("different reparse_point IDX/$FN:%x, MFT/$FN:%x\n",
				idx_fn->reparse_point_tag,
				mft_fn->reparse_point_tag);
		diff = TRUE;
	}

	if (diff == FALSE)
		return;

	ntfs_log_debug("======== START %llu ================\n", ni->mft_no);
	ntfs_log_debug("inode ctime:%llx, mtime:%llx, mftime:%llx, atime:%llx\n",
			ni->creation_time, ni->last_data_change_time,
			ni->last_mft_change_time, ni->last_access_time);
	ntfs_log_debug("std_info ctime:%llx, mtime:%llx, mftime:%llx, atime:%llx\n",
			si_ctime, si_mtime, si_mtime_mft, si_atime);
	ntfs_log_debug("mft_fn ctime:%llx, mtime:%llx, mftime:%llx, atime:%llx\n",
			mft_fn->creation_time, mft_fn->last_data_change_time,
			mft_fn->last_mft_change_time, mft_fn->last_access_time);
	ntfs_log_debug("idx_fn ctime:%llx, mtime:%llx, mftime:%llx, atime:%llx\n",
			idx_fn->creation_time, idx_fn->last_data_change_time,
			idx_fn->last_mft_change_time, idx_fn->last_access_time);
	ntfs_log_debug("======== END =======================\n");

	return;
}
#endif

struct dir {
	struct ntfs_list_head list;
	ntfs_inode *ni;
};

struct ntfsls_dirent {
	ntfs_volume *vol;
};

NTFS_LIST_HEAD(ntfs_dirs_list);


/*
 * check $FILE_NAME attribute in directory index and same one in MFT entry
 * @ni : MFT entry inode
 * @ie : index entry of file (parent's index)
 * @ictx : index context for lookup, not for ni. It's context of ni's parent
 */
static int ntfsck_check_file_name_attr(ntfs_inode *ni, INDEX_ENTRY *ie,
		ntfs_index_context *ictx)
{
	ntfs_volume *vol = ni->vol;
	ntfs_attr_search_ctx *actx = NULL;
	MFT_REF mref = le64_to_cpu(ie->indexed_file);
	FILE_NAME_ATTR *fn,
		       *first_fn = NULL;
	FILE_NAME_ATTR *ie_fn = (FILE_NAME_ATTR *)&ie->key;
	ATTR_RECORD *attr;
	char *filename;
	int ret = -EIO;
	BOOL need_fix = FALSE;

	actx = ntfs_attr_get_search_ctx(ni, NULL);
	if (!actx)
		return -ENOMEM;

	while ((ret = ntfs_attr_lookup(AT_FILE_NAME, AT_UNNAMED, 0, CASE_SENSITIVE,
					0, NULL, 0, actx)) == 0) {
		IGNORE_CASE_BOOL case_sensitive = IGNORE_CASE;

		attr = actx->attr;
		fn = (FILE_NAME_ATTR*)((u8*)attr +
				le16_to_cpu(attr->value_offset));
		filename = ntfs_attr_name_get(fn->file_name, fn->file_name_length);
		ntfs_log_verbose("name: '%s'  type: %d\n", filename, fn->file_name_type);

		if (fn->file_name_type == FILE_NAME_POSIX)
			case_sensitive = CASE_SENSITIVE;
		if (fn->file_name_type == ie_fn->file_name_type)
			first_fn = fn;

		if (ntfs_names_are_equal(fn->file_name, fn->file_name_length,
					ie_fn->file_name, ie_fn->file_name_length,
					case_sensitive, vol->upcase,
					vol->upcase_len)) {
			goto found;
		}

		ntfs_attr_name_free(&filename);
	}

	/* NOT FOUND MFT/$FN */
remove_index:
	check_failed("Filename(in $FILE_NAME) in INDEX ENTRY is different with MFT(%ld) ENTRY's one", MREF(mref));
	if (ntfsck_ask_repair(vol)) {
		ictx->entry = ie;
		ret = ntfs_index_rm(ictx);
		if (ret)
			ntfs_log_error("Failed to remove index entry, mft-no : %ld",
					MREF(mref));
		else {
			ret = ntfsck_update_index_entry(ictx);
			if (ret)
				ntfs_log_error("ntfsck_update_index_entry failed. ret : %d\n", ret);
		}

		if (first_fn) {
			ret = ntfs_index_add_filename(ictx->actx->ntfs_ino,
					first_fn, mref);
			if (ret)
				ntfs_log_error("Failed to add index entry, mft-no : %ld\n",
						MREF(mref));
			else
				--errors;
		}
	}

	ntfs_attr_put_search_ctx(actx);
	return ret;

found:
	/* FOUND!! MFT/$FN about IDX/$FN */

	ret = 0;
	/* check parent MFT reference */
	if (ie_fn->parent_directory != fn->parent_directory) {
		u64 idx_pdir;		/* IDX/$FN's parent MFT no */
		u64 mft_pdir;		/* MFT/$FN's parent MFT no */
		u16 idx_pdir_seq;	/* IDX/$FN's parent MFT sequence no */
		u16 mft_pdir_seq;	/* MFT/$FN's parent MFT sequence no */

		idx_pdir = MREF_LE(ie_fn->parent_directory);
		mft_pdir = MREF_LE(fn->parent_directory);
		idx_pdir_seq = MSEQNO_LE(ie_fn->parent_directory);
		mft_pdir_seq = MSEQNO_LE(fn->parent_directory);

		if (mft_pdir != ictx->ni->mft_no) {
			/* parent MFT entry is not matched! */
			/* Remove this IDX/$FN and,
			 * TODO: Should add IDX/$FN for MFT/$FN in it's parent index */
			ntfs_attr_name_free(&filename);
			first_fn = fn;	/* add $FN to IDX after remove wrong index. */
			goto remove_index;
		}

		if (idx_pdir != mft_pdir || idx_pdir_seq != mft_pdir_seq) {
			check_failed("Parent MFT's sequence No. is differnt "
					"(IDX/$FN:%u MFT/$FN:%u) "
					"on inode(%llu, %s)",
					idx_pdir_seq, mft_pdir_seq,
					(unsigned long long)ni->mft_no, filename);
			need_fix = TRUE;
			goto fix_index;
		}
	}

	/* check $FN size fields */
	if (ie_fn->allocated_size != fn->allocated_size) {
		check_failed("Allocated size is different "
			" (IDX/$FN:%llu MFT/$FN:%llu) "
			"on inode(%llu, %s)",
			(unsigned long long)sle64_to_cpu(ie_fn->allocated_size),
			(unsigned long long)sle64_to_cpu(fn->allocated_size),
			(unsigned long long)ni->mft_no, filename);
		need_fix = TRUE;
		goto fix_index;
	}

	if (ie_fn->data_size != fn->data_size) {
		check_failed("Data size is different "
			"(IDX/$FN:%llu MFT/$FN:%llu) "
			"on inode(%llu, %s)",
			(unsigned long long)sle64_to_cpu(ie_fn->data_size),
			(unsigned long long)sle64_to_cpu(fn->data_size),
			(unsigned long long)ni->mft_no, filename);
		need_fix = TRUE;
		goto fix_index;
	}

	/* check reparse point */
	if (fn->file_attributes & FILE_ATTR_REPARSE_POINT) {
		if (ie_fn->reparse_point_tag != fn->reparse_point_tag) {
			check_failed("Reparse tag is different "
				"(IDX/$FN:%08lx MFT/$FN:%08lx) "
				"on inode(%llu, %s)",
				(long)le32_to_cpu(ie_fn->reparse_point_tag),
				(long)le32_to_cpu(fn->reparse_point_tag),
				(unsigned long long)ni->mft_no, filename);
			need_fix = TRUE;
			goto fix_index;
		}
	}

	/* set NI_FileNameDirty in ni->state to sync
	 * $FILE_NAME attrib when ntfs_inode_close() is called */
fix_index:
	if (need_fix) {
		if (ntfsck_ask_repair(vol)) {
			NInoFileNameSetDirty(ni);
			NInoSetDirty(ni);
			ntfs_inode_update_times(ictx->ni, NTFS_UPDATE_CTIME);

			/* CHECK: copy all MFT/$FN field to IDX/$FN */
			memcpy(ie_fn, fn, sizeof(FILE_NAME_ATTR) - sizeof(ntfschar));
			ret = ntfsck_update_index_entry(ictx);
			if (!ret)
				errors--;
		}
	}

#if DEBUG
	ntfsck_debug_print_fn_attr(actx, ie_fn, fn);
#endif

	ntfs_attr_name_free(&filename);
	ntfs_attr_put_search_ctx(actx);
	return ret;

}

static int ntfsck_add_dir_list(ntfs_volume *vol, INDEX_ENTRY *ie,
			       ntfs_index_context *ictx)
{
	char *filename;
	ntfs_inode *ni;
	struct dir *dir;
	MFT_REF mref;
	int ret = 0;
	FILE_NAME_ATTR *ie_fn = (FILE_NAME_ATTR *)&ie->key;

	if (!ie)
		return -1;

	mref = le64_to_cpu(ie->indexed_file);
	filename = ntfs_attr_name_get(ie_fn->file_name, ie_fn->file_name_length);
	ntfs_log_verbose("%ld, %s\n", MREF(mref), filename);
	ni = ntfs_inode_open(vol, MREF(mref));
	if (ni) {
		if (MREF(mref) >> 3 > fsck_mft_bmp_size) {
			s64 off = fsck_mft_bmp_size;

			fsck_mft_bmp_size +=
				((MREF(mref) >> 3) + 1 + (NTFS_BLOCK_SIZE - 1)) &
				 ~(NTFS_BLOCK_SIZE - 1);
			fsck_mft_bmp = ntfs_realloc(fsck_mft_bmp,
					fsck_mft_bmp_size);
			memset(fsck_mft_bmp + off, 0, fsck_mft_bmp_size - off);
		}

		ntfsck_check_file_name_attr(ni, ie, ictx);

		ntfs_bit_set(fsck_mft_bmp, MREF(mref), 1);

		if ((ie->key.file_name.file_attributes &
		     FILE_ATTR_I30_INDEX_PRESENT) && strcmp(filename, ".") &&
		     strcmp(filename, "./") && strcmp(filename, "..") &&
		     strcmp(filename, "../")) {
			dir = (struct dir *)calloc(1, sizeof(struct dir));
			if (!dir) {
				ntfs_log_error("Failed to allocate for subdir.\n");
				ret = -1;
				goto err_out;
			}

			dir->ni = ni;
			ntfs_list_add_tail(&dir->list, &ntfs_dirs_list);
		}
	} else {
		check_failed("mft entry(%ld) is corrupted, Removing index entry", MREF(mref));
		if (ntfsck_ask_repair(vol)) {
			ictx->entry = ie;
			ret = ntfs_index_rm(ictx);
			if (ret) {
				ntfs_log_error("Failed to remove index entry, mft-no : %ld, filename : %s\n",
						MREF(mref), filename);
			} else {
				ntfs_log_verbose("Index entry that have mft no : %ld, filename %s is deleted\n",
						MREF(mref), filename);
				ret = 1;
				errors--;
			}
		}
	}

err_out:
	return ret;
}

static int ntfsck_scan_index_entries_btree(ntfs_volume *vol)
{
	ntfs_inode *ni;
	struct dir *dir;
	INDEX_ROOT *ir;
	INDEX_ENTRY *next;
	ntfs_attr_search_ctx *ctx = NULL;
	ntfs_index_context *ictx;
	int ret;
	COLLATION_RULES cr;

	dir = (struct dir *)calloc(1, sizeof(struct dir));
	if (!dir) {
		ntfs_log_error("Failed to allocate for subdir.\n");
		return 1;
	}

	ni = ntfs_inode_open(vol, FILE_root);
	if (!ni) {
		ntfs_log_error("Couldn't open the root directory.\n");
		free(dir);
		return 1;
	}

	dir->ni = ni;
	ntfs_list_add(&dir->list, &ntfs_dirs_list);

	while (!ntfs_list_empty(&ntfs_dirs_list)) {
		dir = ntfs_list_entry(ntfs_dirs_list.next, struct dir, list);

		ctx = ntfs_attr_get_search_ctx(dir->ni, NULL);
		if (!ctx)
			goto err_out;

		/* Find the index root attribute in the mft record. */
		if (ntfs_attr_lookup(AT_INDEX_ROOT, NTFS_INDEX_I30, 4, CASE_SENSITIVE, 0, NULL,
					0, ctx)) {
			ntfs_log_perror("Index root attribute missing in directory inode "
					"%lld", (unsigned long long)dir->ni->mft_no);
			ntfs_attr_put_search_ctx(ctx);
			goto err_out;
		}

		/* Get to the index root value. */
		ir = (INDEX_ROOT*)((u8*)ctx->attr +
				le16_to_cpu(ctx->attr->value_offset));

		cr = ir->collation_rule;

		ictx = ntfs_index_ctx_get(dir->ni, NTFS_INDEX_I30, 4);
		if (!ictx) {
			ntfs_attr_put_search_ctx(ctx);
			goto err_out;
		}

		ictx->ir = ir;
		ictx->actx = ctx;
		ictx->parent_vcn[ictx->pindex] = VCN_INDEX_ROOT_PARENT;
		ictx->is_in_root = TRUE;
		ictx->parent_pos[ictx->pindex] = 0;

		ictx->block_size = le32_to_cpu(ir->index_block_size);
		if (ictx->block_size < NTFS_BLOCK_SIZE) {
			ntfs_log_perror("Index block size (%d) is smaller than the "
					"sector size (%d)", ictx->block_size, NTFS_BLOCK_SIZE);
			goto err_out;
		}

		if (vol->cluster_size <= ictx->block_size)
			ictx->vcn_size_bits = vol->cluster_size_bits;
		else
			ictx->vcn_size_bits = NTFS_BLOCK_SIZE_BITS;

		/* The first index entry. */
		next = (INDEX_ENTRY*)((u8*)&ir->index +
				le32_to_cpu(ir->index.entries_offset));

		ret = ntfs_index_entry_inconsistent(vol, next, cr, 0, ictx);
		if (ret > 0) {
			ret = ntfsck_update_index_entry(ictx);
			if (ret) {
				errors++;
				goto err_out;
			}
		}
		if (next->ie_flags & INDEX_ENTRY_NODE) {
			ictx->ia_na= ntfs_attr_open(dir->ni, AT_INDEX_ALLOCATION,
						    ictx->name, ictx->name_len);
			if (!ictx->ia_na) {
				ntfs_log_perror("Failed to open index allocation of inode "
						"%llu", (unsigned long long)dir->ni->mft_no);
				ntfs_attr_put_search_ctx(ctx);
				goto err_out;
			} else {
				next = ntfs_index_walk_down(next, ictx);
				if (!next)
					goto next_dir;
			}
		}

		if (!(next->ie_flags & INDEX_ENTRY_END))
			goto add_dir_list;

		while ((next = ntfs_index_next(next, ictx)) != NULL) {
add_dir_list:
			ret = ntfsck_add_dir_list(vol, next, ictx);
			if (ret) {
				next = ictx->entry;
				if (ret < 0)
					break;
				if (!(next->ie_flags & INDEX_ENTRY_END))
					goto add_dir_list;
			}
		}

next_dir:
		ntfs_inode_mark_dirty(ictx->actx->ntfs_ino);
		ntfs_index_ctx_put(ictx);
		ntfs_inode_close(dir->ni);
		ntfs_list_del(&dir->list);
		free(dir);
	}

	return 0;
err_out:
	return -1;
}

/**
 * list_dir_entry
 *
 * FIXME: Should we print errors as we go along? (AIA)
 */
static int list_dir_entry(struct ntfsls_dirent *dirent, const ntfschar *name,
			  const int name_len, const int name_type,
			  const s64 pos __attribute__((unused)),
			  const MFT_REF mref, const unsigned int dt_type)
{
	char *filename = NULL;
	int result = 0;
	struct dir *dir = NULL;
	ntfs_inode *ni;
	ntfs_volume *vol = dirent->vol;

	filename = calloc(1, MAX_PATH);
	if (!filename)
		return -1;

	if (ntfs_ucstombs(name, name_len, &filename, MAX_PATH) < 0) {
		ntfs_log_error("Cannot represent filename in current locale.\n");
		goto free;
	}

	if (MREF(mref) < FILE_first_user)
		goto free;

	ntfs_log_verbose("%7llu %s\n", (unsigned long long)MREF(mref), filename);
	ni = ntfs_inode_open(vol, MREF(mref));
	if (ni) {
		if (dt_type == NTFS_DT_DIR &&
		    strcmp(filename, ".") && strcmp(filename, "./") &&
		    strcmp(filename, "..") && strcmp(filename, "../")) {
			dir = (struct dir *)calloc(1, sizeof(struct dir));
			if (!dir) {
				ntfs_log_error("Failed to allocate for subdir.\n");
				result = -1;
				goto free;
			}

			dir->ni = ni;
			ntfs_list_add_tail(&dir->list, &ntfs_dirs_list);
		}
	}

free:
	free(filename);
	return result;
}

static int ntfsck_scan_index_entries_bitmap(ntfs_volume *vol)
{
	ntfs_inode *ni;
	struct dir *dir;
	struct ntfsls_dirent dirent;
	int result;

	dir = (struct dir *)calloc(1, sizeof(struct dir));
	if (!dir) {
		ntfs_log_error("Failed to allocate for subdir.\n");
		goto error_exit;
	}

	ni = ntfs_inode_open(vol, FILE_root);
	if (!ni) {
		ntfs_log_error("Couldn't open the root directory.\n");
		free(dir);
		return 1;
	}

	dir->ni = ni;
	ntfs_list_add(&dir->list, &ntfs_dirs_list);

	/* Scan all index entries through mft entries */
	while (!ntfs_list_empty(&ntfs_dirs_list)) {
		s64 pos = 0;

		dir = ntfs_list_entry(ntfs_dirs_list.next, struct dir, list);

		memset(&dirent, 0, sizeof(dirent));
                dirent.vol = vol;
		result = ntfs_readdir(dir->ni, &pos, &dirent, (ntfs_filldir_t)list_dir_entry);
		if (result)
			check_failed("ntfs_readdir failed(%d)\n", errno);

		ntfs_inode_close(dir->ni);
		ntfs_list_del(&dir->list);
		free(dir);
	}

	return 0;
error_exit:
	return 1;
}


static int ntfsck_scan_index_entries(ntfs_volume *vol)
{
	int result;

	ntfs_log_info("Parse #%d: Check index entries in volume...\n", parse_count++);

	result = ntfsck_scan_index_entries_btree(vol);
	if (!result)
		result = ntfsck_scan_index_entries_bitmap(vol);

	return result;
}

static void ntfsck_check_mft_records(ntfs_volume *vol)
{
	s64 mft_num, nr_mft_records;

	ntfs_log_info("Parse #%d: Check mft entries in volume...\n", parse_count++);

	// For each mft record, verify that it contains a valid file record.
	nr_mft_records = vol->mft_na->initialized_size >>
			vol->mft_record_size_bits;
	ntfs_log_verbose("Checking %lld MFT records.\n", (long long)nr_mft_records);

	for (mft_num = FILE_first_user; mft_num < nr_mft_records; mft_num++) {
		ntfsck_verify_mft_record(vol, mft_num);
	}
}

static int ntfsck_reset_dirty(ntfs_volume *vol)
{
	le16 flags;

	if (!(vol->flags | VOLUME_IS_DIRTY))
		return 0;

	ntfs_log_verbose("Resetting dirty flag.\n");

	flags = vol->flags & ~VOLUME_IS_DIRTY;

	if (ntfs_volume_write_flags(vol, flags)) {
		ntfs_log_error("Error setting volume flags.\n");
		return -1;
	}
	return 0;
}

static int ntfsck_replay_log(ntfs_volume *vol __attribute__((unused)))
{
	ntfs_log_info("Parse #%d: Replay logfile...\n", parse_count++);

	/*
	 * For now, Just reset logfile.
	 */
	if (ntfs_logfile_reset(vol)) {
		ntfs_log_error("ntfs logfile reset failed, errno : %d\n", errno);
		errors++;
		return -1;
	}

	return 0;
}

static ntfs_volume *ntfsck_check_system_files_and_mount(struct ntfs_device *dev,
		ntfs_mount_flags flags)
{
	ntfs_inode *ni;
	ntfs_volume *vol;
	s64 mft_num;

	ntfs_log_info("Parse #%d: Check check system files...\n", parse_count++);

	/* Call ntfs_device_mount() to do the actual mount. */
	vol = ntfs_device_mount(dev, option.flags);
	if (!vol)
		return vol;

	fsck_lcn_bitmap_size = NTFS_BLOCK_SIZE;
	fsck_lcn_bitmap = ntfs_calloc(NTFS_BLOCK_SIZE);
	if (!fsck_lcn_bitmap) {
		ntfs_umount(vol, FALSE);
		return NULL;
	}

	fsck_mft_bmp_size = NTFS_BLOCK_SIZE;
	fsck_mft_bmp = ntfs_calloc(fsck_mft_bmp_size);
	if (!fsck_mft_bmp) {
		free(fsck_lcn_bitmap);
		ntfs_umount(vol, FALSE);
		return NULL;
	}

	/*
	 * System MFT entries should be verified checked by ntfs_device_mount().
	 * Here just account number of clusters that is used by system MFT
	 * entries.
	 */
	for (mft_num = 0; mft_num < FILE_first_user; mft_num++) {

		ni = ntfs_inode_open(vol, mft_num);
		if (ni)
			ntfsck_update_lcn_bitmap(ni);
	}

	return vol;
}

/**
 * main - Does just what C99 claim it does.
 *
 * For more details on arguments and results, check the man page.
 */
int main(int argc, char **argv)
{
	struct ntfs_device *dev;
	ntfs_volume *vol;
	const char *name;
	int c;
	unsigned long mnt_flags;

	ntfs_log_set_handler(ntfs_log_handler_outerr);
	if (argc == 1 || argc > 3) {
		usage(1);
		return RETURN_USAGE_OR_SYNTAX_ERROR;
	}

	if (argc == 2)
		name = argv[1];
	else
		name = argv[2];

	option.flags = NTFS_MNT_FS_ASK_REPAIR;
	option.verbose = 0;
	while ((c = getopt_long(argc, argv, "anpyhvV", opts, NULL)) != EOF) {
		switch (c) {
		case 'a':
		case 'p':
			option.flags = NTFS_MNT_FS_AUTO_REPAIR;
			break;
		case 'n':
			option.flags = NTFS_MNT_FS_NO_REPAIR | NTFS_MNT_RDONLY;
			break;
		case 'r':
			option.flags = NTFS_MNT_FS_ASK_REPAIR;
			break;
		case 'y':
			option.flags = NTFS_MNT_FS_YES_REPAIR;
			break;
		case 'h':
			usage(0);
		case '?':
			usage(1);
			break;
		case 'v':
			option.verbose = 1;
                        ntfs_log_set_levels(NTFS_LOG_LEVEL_VERBOSE);
                        break;
		case 'V':
			version();
			break;
		default:
			ntfs_log_info("ERROR: Unknown option '%s'.\n", argv[optind - 1]);
			usage(1);
		}
	}

	if (!ntfs_check_if_mounted(name, &mnt_flags)) {
		if ((mnt_flags & NTFS_MF_MOUNTED)) {
			if (!(mnt_flags & NTFS_MF_READONLY)) {
				ntfs_log_error("Refusing to operate on read-write mounted device %s.\n",
						name);
				exit(1);
			}

			if (option.flags != (NTFS_MNT_FS_NO_REPAIR | NTFS_MNT_RDONLY)) {
				ntfs_log_error("Refusing to change filesystem on read mounted device %s.\n",
						name);
				exit(1);
			}
		}
	} else
		ntfs_log_perror("Failed to determine whether %s is mounted",
				name);

	/* Allocate an ntfs_device structure. */
	dev = ntfs_device_alloc(name, 0, &ntfs_device_default_io_ops, NULL);
	if (!dev)
		return RETURN_OPERATIONAL_ERROR;

	vol = ntfsck_check_system_files_and_mount(dev, option.flags);
	if (!vol) {
		ntfs_device_free(dev);
		return 2;
	}

	if (ntfsck_replay_log(vol))
		goto err_out;

	if (vol->flags & VOLUME_IS_DIRTY)
		ntfs_log_warning("Volume is dirty.\n");

	if (ntfsck_scan_index_entries(vol)) {
		ntfs_log_error("Stop processing fsck due to critical problems\n");
		goto err_out;
	}

	ntfsck_check_mft_records(vol);

	ntfsck_check_orphaned_clusters(vol);

	if (errors)
		ntfs_log_info("%d errors found.\n", errors);
	else
		ntfs_log_info("Clean, No errors found\n");

	if (!errors)
		ntfsck_reset_dirty(vol);

err_out:
	ntfs_umount(vol, FALSE);

	if (errors)
		return 1;
	return 0;
}

