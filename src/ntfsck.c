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
#include "lcnalloc.h"

#define RETURN_FS_NO_ERRORS (0)
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

struct dir {
	struct ntfs_list_head list;
	ntfs_inode *ni;
};

struct ntfsls_dirent {
	ntfs_volume *vol;
};

/* runlist allocated size: TODO move to runlist.c */
struct rl_size {
	s64 asize;	/* allocated size (include hole length) */
	s64 real_asize;	/* real allocated size */
	VCN vcn;	/* last valid vcn */
};

NTFS_LIST_HEAD(ntfs_dirs_list);

int parse_count = 1;

#define NTFS_PROGS	"ntfsck"
/**
 * usage
 */
__attribute__((noreturn))
static void usage(int error)
{
	ntfs_log_info("%s v%s (libntfs-3g)\n\n"
		      "Usage: %s [options] device\n"
		      "-a, --repair-auto	auto-repair. no questions\n"
		      "-p,			auto-repair. no questions\n"
		      "-n, --repair-no		just check the consistency and no fix\n"
		      "-r, --repair		Repair interactively\n"
		      "-y, --repair-yes		all yes about all question\n"
		      "-v, --verbose		verbose\n"
		      "-V, --version		version\n\n"
		      "NOTE: -a/-p, -C, -n, -r, -y options are mutually exclusive with each other options\n\n"
		      "For example: %s /dev/sda1\n"
		      "For example: %s -C /dev/sda1\n"
		      "For example: %s -a /dev/sda1\n\n",
		      NTFS_PROGS, VERSION, NTFS_PROGS, NTFS_PROGS, NTFS_PROGS, NTFS_PROGS);
	exit(error ? RETURN_USAGE_OR_SYNTAX_ERROR : 0);
}

/**
 * version
 */
__attribute__((noreturn))
static void version(void)
{
	ntfs_log_info("%s v%s\n\n", NTFS_PROGS, VERSION);
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

static u8 *fsck_mft_bmp;
static s64 fsck_mft_bmp_size;

u8 *fsck_lcn_bitmap;
unsigned int fsck_lcn_bitmap_size;

static FILE_NAME_ATTR *ntfsck_find_file_name_attr(ntfs_inode *ni,
		FILE_NAME_ATTR *ie_fn, ntfs_attr_search_ctx *actx);
static int ntfsck_check_directory(ntfs_inode *ni);
static int ntfsck_check_file(ntfs_inode *ni);
static int ntfsck_setbit_runlist(ntfs_inode *ni, runlist *rl, u8 set_bit,
		struct rl_size *rls);
static int ntfsck_check_inode(ntfs_inode *ni, INDEX_ENTRY *ie,
		ntfs_index_context *ictx);
static int ntfsck_initialize_index_attr(ntfs_inode *ni);

char ntfsck_mft_bmp_bit_get(const u64 bit)
{
	if (bit >> 3 >= fsck_mft_bmp_size)
		return 0;
	return ntfs_bit_get(fsck_mft_bmp, bit);
}

int ntfsck_mft_bmp_bit_set(u64 mft_no)
{
	if (mft_no >> 3 >= fsck_mft_bmp_size) {
		s64 off = fsck_mft_bmp_size;

		fsck_mft_bmp_size =
			((mft_no >> 3) + 1 + (NTFS_BLOCK_SIZE - 1)) &
			~(NTFS_BLOCK_SIZE - 1);

		fsck_mft_bmp = ntfs_realloc(fsck_mft_bmp,
				fsck_mft_bmp_size);
		if (!fsck_mft_bmp) {
			ntfs_log_perror("Can't extend mft bitmap memory(%llu)\n",
					(unsigned long long)mft_no);
			return -ENOMEM;
		}
		memset(fsck_mft_bmp + off, 0, fsck_mft_bmp_size - off);
	}

	ntfs_bit_set(fsck_mft_bmp, mft_no, 1);
	return 0;
}

static int ntfsck_check_backup_boot_sector(ntfs_volume *vol, s64 cl_pos)
{
	NTFS_BOOT_SECTOR *backup_boot;
	s64 backup_boot_pos = cl_pos << vol->cluster_size_bits;

	backup_boot = ntfs_malloc(vol->sector_size);
	if (!backup_boot)
		return -ENOMEM;

	if (ntfs_pread(vol->dev, backup_boot_pos, vol->sector_size, backup_boot) !=
			vol->sector_size) {
		ntfs_log_error("Failed to read boot sector.\n");
		free(backup_boot);
		return -EIO;
	}

	if (!ntfs_boot_sector_is_ntfs(backup_boot)) {
		free(backup_boot);
		return -ENOENT;
	}

	ntfs_log_verbose("Found backup boot sector in "
			 "the middle of the volume(cl_pos : %ld).\n", cl_pos);
	free(backup_boot);
	return 0;
}

static void ntfsck_check_orphaned_clusters(ntfs_volume *vol)
{
	s64 pos = 0, wpos, i, count, written;
	BOOL backup_boot_check = FALSE, repair = FALSE;
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

			if (pos >= fsck_lcn_bitmap_size)
				continue;

			if (fsck_lcn_bitmap[pos] == bm[i])
				continue;

			for (cl = pos * 8; cl < (pos + 1) * 8; cl++) {
				char lbmp_bit, fsck_bmp_bit;

				if (cl >= vol->nr_clusters)
					break;

				lbmp_bit = ntfs_bit_get(bm, i * 8 + cl % 8);
				fsck_bmp_bit = ntfs_bit_get(fsck_lcn_bitmap, cl);
				if (fsck_bmp_bit != lbmp_bit) {
					if (!fsck_bmp_bit && backup_boot_check == FALSE &&
					    cl == vol->nr_clusters / 2) {
						if (!ntfsck_check_backup_boot_sector(vol, cl)) {
							backup_boot_check = TRUE;
							continue;
						}
					}

					if (fsck_bmp_bit == 0 && lbmp_bit == 1) {
						check_failed("Found orphaned cluster bit(%ld) in $Bitmap. Clear it", cl);
					} else {
						check_failed("Found missing cluster bit(%ld) in $Bitmap. Set it", cl);
					}
					if (ntfsck_ask_repair(vol)) {
						ntfs_bit_set(bm, i * 8 + cl % 8, !lbmp_bit);
						repair = TRUE;
						fsck_err_fixed();
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
}

static void ntfsck_set_bitmap_range(u8 *bm, s64 pos, s64 length, u8 bit)
{
	while (length--)
		ntfs_bit_set(bm, pos++, bit);
}

static int ntfsck_set_lcnbmp_range(s64 pos, s64 length, u8 bit)
{
	if (fsck_lcn_bitmap_size <= (pos + length) >> 3) {
		int off = fsck_lcn_bitmap_size;

		fsck_lcn_bitmap_size = (((pos + length) >> 3) + 1 +
			(NTFS_BLOCK_SIZE - 1)) & ~(NTFS_BLOCK_SIZE - 1);
		fsck_lcn_bitmap = ntfs_realloc(fsck_lcn_bitmap,
				fsck_lcn_bitmap_size);
		if (!fsck_lcn_bitmap) {
			ntfs_log_perror("Can't extend lcn bitmap memory\n");
			return -ENOMEM;
		}

		memset(fsck_lcn_bitmap + off, 0, fsck_lcn_bitmap_size - off);
	}

	ntfsck_set_bitmap_range(fsck_lcn_bitmap, pos, length, bit);
	return 0;
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

		rl = ntfs_mapping_pairs_decompress(ni->vol, actx->attr, NULL);
		if (!rl) {
			ntfs_log_error("Failed to decompress runlist(mft_no : %ld, type : 0x%x).  Leaving inconsistent metadata.\n",
					ni->mft_no, actx->attr->type);
			continue;
		}

		while (rl[i].length) {
			if (rl[i].lcn > (LCN)LCN_HOLE) {
				ntfsck_set_lcnbmp_range(rl[i].lcn, rl[i].length, 1);
				ntfs_log_verbose("Cluster run of mft entry(%ld) : lcn : %ld, length : %ld\n",
						ni->mft_no, rl[i].lcn, rl[i].length);
			}
			++i;
		}

		free(rl);
	}

	ntfs_attr_put_search_ctx(actx);

	return 0;
}

/*
 * check runlist size and set/clear bitmap of runlist.
 * Set or clear bit until encountering lcn whose value is less than LCN_HOLE,
 * Clear bit for invalid lcn.
 * (TODO: check duplicated, check $BITMAP if exist)
 *
 * @ni : MFT entry inode
 * @rl : runlist to check
 * @set_bit : bit value for set/clear
 * @rls : structure for runlist length, it contains allocated size and
 *	  real allocated size. it may be NULL, don't return calculated size.
 */
static int ntfsck_setbit_runlist(ntfs_inode *ni, runlist *rl, u8 set_bit,
		struct rl_size *rls)
{
	ntfs_volume *vol;
	s64 rl_asize = 0;	/* rl allocated size (including HOLE length) */
	s64 rl_real_asize = 0;	/* rl real allocated size */
	s64 rsize;		/* a cluster run size */
	VCN valid_vcn = 0;
	int i = 0;

	if (!ni || !rl)
		return STATUS_ERROR;

	vol = ni->vol;

	while (rl && rl[i].length) {
		if (rl[i].lcn > LCN_HOLE) {
			ntfs_log_trace("Cluster run of mtf entry(%ld): "
					"vcn(%ld), lcn(%ld), length(%ld)\n",
					ni->mft_no, rl[i].vcn, rl[i].lcn,
					rl[i].length);

			ntfsck_set_lcnbmp_range(rl[i].lcn, rl[i].length, set_bit);

			if (set_bit == 0)
				ntfs_cluster_free_basic(vol, rl[i].lcn, rl[i].length);

			rsize = rl[i].length << vol->cluster_size_bits;
			rl_real_asize += rsize;
			rl_asize += rsize;

		} else if (rl[i].lcn == LCN_HOLE) {
			rsize = rl[i].length << vol->cluster_size_bits;
			rl_asize += rsize;

		} else {
			/* valid vcn until encountered < LCN_HOLE */
			if (set_bit) {
				valid_vcn = rl_asize >> vol->cluster_size_bits;
				set_bit = 0;
			}

			rl[i].lcn = LCN_ENOENT;
			rl[i].length = 0;
		}

		i++;
	}

	if (!valid_vcn)
		valid_vcn = rl_asize >> vol->cluster_size_bits;

	if (rls) {
		rls->vcn = valid_vcn;
		rls->asize = rl_asize;
		rls->real_asize = rl_real_asize;
	}

	return STATUS_OK;
}

/*
 * set/clear bit all non-resident attributes of inode.
 */
static void ntfsck_check_non_resident_cluster(ntfs_inode *ni, u8 set_bit)
{
	ntfs_attr_search_ctx *ctx;

	ctx = ntfs_attr_get_search_ctx(ni, NULL);
	while (!ntfs_attrs_walk(ctx)) {
		if (!ctx->attr->non_resident)
			continue;

		runlist *rl;

		/* TODO: how to handle if attribute's runlist has corrupted? */
		rl = ntfs_mapping_pairs_decompress(ni->vol, ctx->attr, NULL);
		if (!rl) {
			ntfs_log_error("Failed to decompress runlist. "
					"Leaving inconsistent metadata.\n");
			continue;
		}

		if (ntfsck_setbit_runlist(ni, rl, set_bit, NULL)) {
			ntfs_log_error("Failed to check and setbit runlist. "
					"Leaving inconsistent metadata.\n");
			/* continue */
		}
		free(rl);
	}

	ntfs_attr_put_search_ctx(ctx);
}

/*
 * do not call ntfs_inode_close() after this function called,
 * because ntfs_inode_close() is called in ntfs_mft_record_free().
 * */
static void ntfsck_free_mft_records(ntfs_volume *vol, ntfs_inode *ni)
{
	ntfs_inode_attach_all_extents(ni);
	while (ni->nr_extents) {
		if (ntfs_mft_record_free(vol, *(ni->extent_nis)))
			ntfs_log_error("Failed to free extent MFT record(%llu). "
					"Leaving inconsistent metadata.\n",
					(unsigned long long)ni->mft_no);
	}

	if (ntfs_mft_record_free(vol, ni))
		ntfs_log_error("Failed to free MFT record(%llu). "
				"Leaving inconsistent metadata. Run chkdsk.\n",
				(unsigned long long)ni->mft_no);
}

/* only called from repairing orphaned file */
static int ntfsck_find_and_check_index(ntfs_inode *parent_ni, ntfs_inode *ni,
		FILE_NAME_ATTR *fn)
{
	ntfs_index_context *ictx;
	ntfs_volume *vol;

	if (!parent_ni || !ni || !fn)
		return STATUS_ERROR;

	vol = ni->vol;

	ictx = ntfs_index_ctx_get(parent_ni, NTFS_INDEX_I30, 4);
	if (!ictx) {
		ntfs_log_perror("Failed to get index ctx, inode(%llu) "
				"for repairing orphan inode",
				(unsigned long long)parent_ni->mft_no);
		return STATUS_ERROR;
	}

	if (!ntfs_index_lookup(fn, sizeof(FILE_NAME_ATTR), ictx)) {

		/* Find index */
		if (ntfsck_check_inode(ni, ictx->entry, ictx)) {
			/* Inode check failed, remove index and inode */
			ntfs_log_info("Failed to check inode(%lld) "
					"for repairing orphan inode\n",
					(unsigned long long)ni->mft_no);

			if (ntfs_index_rm(ictx)) {
				ntfs_log_error("Failed to remove index entry of inode(%llu)\n",
						(unsigned long long)ni->mft_no);
				ntfs_index_ctx_put(ictx);
				return STATUS_ERROR;
			}
			ntfs_inode_mark_dirty(ictx->ni);
			ntfsck_check_non_resident_cluster(ni, 0);
			ntfsck_free_mft_records(vol, ni);

			ntfs_index_ctx_put(ictx);
			return STATUS_ERROR;
		}

	} else {
		ntfs_index_ctx_put(ictx);
		return STATUS_NOT_FOUND;
	}

	ntfs_index_ctx_put(ictx);
	return STATUS_OK;
}

static int ntfsck_add_index_entry_orphaned_file(ntfs_volume *vol, s64 mft_no)
{
	ntfs_attr_search_ctx *ctx;
	FILE_NAME_ATTR *fn;
	ntfs_inode *parent_ni = NULL;
	ntfs_inode *ni = NULL;
	u64 parent_no;
	struct orphan_mft {
		s64 mft_no;
		struct ntfs_list_head list;
	};
	NTFS_LIST_HEAD(ntfs_orphan_list);
	struct orphan_mft *of;
	int err = 0;

stack_of:
	of = (struct orphan_mft *)calloc(1, sizeof(struct orphan_mft));
	if (!of)
		return -ENOMEM;

	of->mft_no = mft_no;
	ntfs_list_add(&of->list, &ntfs_orphan_list);

	while (!ntfs_list_empty(&ntfs_orphan_list)) {
		of = ntfs_list_entry(ntfs_orphan_list.next, struct orphan_mft, list);

		if (err) {
			err = 0;
			goto delete_inodes;
		}

		ni = ntfs_inode_open(vol, of->mft_no);
		if (!ni)
			goto delete_inodes;

		ctx = ntfs_attr_get_search_ctx(ni, NULL);
		if (!ctx) {
			ntfs_log_error("Failed to allocate attribute context\n");
			goto delete_inodes;
		}

		err = ntfs_attr_lookup(AT_FILE_NAME, AT_UNNAMED, 0,
						CASE_SENSITIVE, 0, NULL, 0, ctx);
		if (err) {
			/* $FILE_NAME lookup failed */
			ntfs_log_error("Failed to lookup $FILE_NAME, Remove inode(%llu)\n",
					(unsigned long long)ni->mft_no);
			err = 0;
			goto delete_inodes;
		}

		/* We know this will always be resident. */
		fn = (FILE_NAME_ATTR *)((u8 *)ctx->attr +
				le16_to_cpu(ctx->attr->value_offset));

		parent_no = le64_to_cpu(fn->parent_directory);

		/* skip if parent is system file */
		if (MREF(parent_no) < FILE_first_user)
			goto delete_inodes;

		/*
		 * Consider that the parent could be orphaned.
		 */

		/* TODO: modify condition for finding orphan file? */
		if (!ntfsck_mft_bmp_bit_get(MREF(parent_no))) {
			if (utils_mftrec_in_use(vol, MREF(parent_no))) {
				/*
				 * Do not delete inode on orphan list
				 * and check parent inode
				 * */
				ntfs_attr_put_search_ctx(ctx);
				ctx = NULL;
				ntfs_inode_close(ni);
				mft_no = MREF(parent_no);
				goto stack_of;
			}

			/*
			 * Parent inode is deleted! Now delete sub-inodes of it.
			 * TODO: Add inode whose parent inode was deleted,
			 *	 to root directory.
			 */
			ntfs_log_info("!! FOUND Deleted parent inode(%llu), inode(%llu)\n",
					(unsigned long long)MREF(parent_no),
					(unsigned long long)ni->mft_no);

delete_inodes:
			if (ni) {
				ntfsck_check_non_resident_cluster(ni, 0);
				ntfsck_free_mft_records(vol, ni);
			}
			ntfs_list_del(&of->list);
			free(of);

			while (!ntfs_list_empty(&ntfs_orphan_list)) {
				of = ntfs_list_entry(ntfs_orphan_list.next, struct orphan_mft, list);
				ni = ntfs_inode_open(vol, of->mft_no);
				if (!ni) {
					ntfs_list_del(&of->list);
					free(of);
					err = -EIO;
					continue;
				}
				ntfs_log_info(" delete inode(%llu)\n",
						(unsigned long long)ni->mft_no);

				ntfsck_check_non_resident_cluster(ni, 0);
				ntfsck_free_mft_records(vol, ni);
				ntfs_list_del(&of->list);
				free(of);
			}

			ntfs_attr_put_search_ctx(ctx);
			return err;
		}

		/*
		 * Add orphan inode to parent
		 */

		if (parent_no != (u64)-1)
			parent_ni = ntfs_inode_open(vol, MREF(parent_no));

		if (parent_ni) {
			int ret = -1;

			/* Check parent inode */
			if (ntfsck_check_directory(parent_ni)) {
				ntfs_log_error("Failed to check parent directory(%lld) "
						"for repairing orphan inode\n",
						(unsigned long long)ni->mft_no);
				goto delete_inodes;
			}

			/* Add index for orphaned inode */
			if (ni->mrec->flags & MFT_RECORD_IS_DIRECTORY) {
				ntfsck_initialize_index_attr(ni);

				fn->allocated_size = 0;
				fn->data_size = 0;
				ni->allocated_size = 0;
				ni->data_size = 0;
				ntfs_inode_mark_dirty(ni);
			}

			ret = ntfsck_find_and_check_index(parent_ni, ni, fn);
			if (ret == STATUS_OK)
				goto next_item;
			else if (ret == STATUS_ERROR) {
				err = -EIO;
				ni = NULL;
				goto delete_inodes;
			}

			/* Not found index for $FN */

			err = ntfs_index_add_filename(parent_ni, fn,
					MK_MREF(ni->mft_no,
						le16_to_cpu(ni->mrec->sequence_number)));
			if (err) {
				ntfs_log_error("Failed to add index(%llu) to parent(%llu) "
						"err(%d)\n",
						(unsigned long long)ni->mft_no,
						(unsigned long long)parent_ni->mft_no, err);
				err = -EIO;
				goto delete_inodes;
			}

			/* check again after adding $FN to index */
			ret = ntfsck_find_and_check_index(parent_ni, ni, fn);
			if (ret == STATUS_ERROR || ret == STATUS_NOT_FOUND) {
				err = -EIO;
				ni = NULL;
				goto delete_inodes;
			}

			ntfs_bit_set(fsck_mft_bmp, ni->mft_no, 1);

			ntfsck_update_lcn_bitmap(ni);
			/*
			 * Recall ntfsck_update_lcn_bitmap() about parent_ni.
			 * Because cluster can be allocated by adding index entry.
			 */
			ntfsck_update_lcn_bitmap(parent_ni);

		} /* if (parent_ni) */

next_item:
		if (ctx) {
			ntfs_attr_put_search_ctx(ctx);
			ctx = NULL;
		}

		if (parent_ni) {
			ntfs_inode_close(parent_ni);
			parent_ni = NULL;
		}

		if (ni) {
			ntfs_inode_close(ni);
			ni = NULL;
		}

		ntfs_list_del(&of->list);
		free(of);
	} /* while (!ntfs_list_empty(&ntfs_orphan_list)) */

	return err;
}

static void ntfsck_verify_mft_record(ntfs_volume *vol, s64 mft_num)
{
	int is_used;
	int always_exist_sys_meta_num = vol->major_ver >= 3 ? 11 : 10;
	ntfs_inode *ni;
	s64 mft_no = -1;

	is_used = utils_mftrec_in_use(vol, mft_num);
	if (is_used < 0) {
		check_failed("Error getting bit value for record %lld.\n",
			(long long)mft_num);
		return;
	} else if (!is_used) {
		if (mft_num <= always_exist_sys_meta_num) {
			check_failed("Record %lld unused. Fixing or fail about system files.\n",
					(long long)mft_num);
			return;
		}

		ntfs_log_verbose("Record %lld unused. Skipping.\n",
				(long long)mft_num);
		return;
	}

	ntfs_log_verbose("MFT record %lld\n", (long long)mft_num);

	ni = ntfs_inode_open(vol, mft_num);
	is_used = ntfsck_mft_bmp_bit_get(mft_num);
	/*
	 * If !ni and is_used is true, This mft number is external mft.
	 * In the base mft entry, this will already be checked, so there
	 * is no need to check it anymore.
	 */
	if (!ni && is_used)
		return;

	if (!ni) {
		check_failed("Clear the bit of mft no(%ld) in the $MFT/$BITMAP corresponding orphaned MFT record",
				mft_num);
		if (ntfsck_ask_repair(vol)) {
			if (ntfs_bitmap_clear_bit(vol->mftbmp_na, mft_num)) {
				ntfs_log_error("ntfs_bitmap_clear_bit failed, errno : %d\n",
						errno);
				return;
			}
			fsck_err_fixed();
		}
		return;
	}

	mft_no = ni->mft_no;
	if (!is_used) {
		check_failed("Found an orphaned file(mft no: %ld). Try to add index entry",
				mft_num);
		if (ntfsck_ask_repair(vol)) {
			/* close inode to avoid nested call of ntfs_inode_open() */
			ntfs_inode_close(ni);

			/* TODO: Move orphan mft entry to lost+found directory */
			if (ntfsck_add_index_entry_orphaned_file(vol, mft_no)) {
				/*
				 * error returned.
				 * inode is already freed and closed in that function,
				 * do not need to call ntfs_inode_close()
				 */
				return;
			}
			fsck_err_fixed();
		} else {
			/*
			 * Update number of clusters that is used for each
			 * non-resident mft entries to bitmap.
			 */
			ntfsck_update_lcn_bitmap(ni);
			ntfs_inode_close(ni);
		}
	} else {
		ntfsck_update_lcn_bitmap(ni);
		ntfs_inode_close(ni);
	}
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
		ntfs_log_info("STD TIME != MFT/$FN\n");
		diff = TRUE;
	}

	if (si_mtime != ni->last_data_change_time ||
			si_mtime_mft != ni->last_mft_change_time) {
		ntfs_log_info("STD TIME != INODE\n");
		diff = TRUE;
	}

	if (si_mtime != idx_fn->last_data_change_time ||
			si_mtime_mft != idx_fn->last_mft_change_time) {
		ntfs_log_info("STD TIME != IDX/$FN\n");
		diff = TRUE;
	}

	if (idx_fn->parent_directory != mft_fn->parent_directory) {
		ntfs_log_info("different parent_directory IDX/$FN, MFT/$FN\n");
		diff = TRUE;
	}
	if (idx_fn->allocated_size != mft_fn->allocated_size) {
		ntfs_log_info("different allocated_size IDX/$FN, MFT/$FN\n");
		diff = TRUE;
	}
	if (idx_fn->allocated_size != mft_fn->allocated_size) {
		ntfs_log_info("different allocated_size IDX/$FN, MFT/$FN\n");
		diff = TRUE;
	}
	if (idx_fn->data_size != mft_fn->data_size) {
		ntfs_log_info("different data_size IDX/$FN, MFT/$FN\n");
		diff = TRUE;
	}

	if (idx_fn->reparse_point_tag != mft_fn->reparse_point_tag) {
		ntfs_log_info("different reparse_point IDX/$FN:%x, MFT/$FN:%x\n",
				idx_fn->reparse_point_tag,
				mft_fn->reparse_point_tag);
		diff = TRUE;
	}

	if (diff == FALSE)
		return;

	ntfs_log_info("======== START %llu ================\n",
			(unsigned long long)ni->mft_no);
	ntfs_log_info("inode ctime:%llx, mtime:%llx, mftime:%llx, atime:%llx\n",
			(unsigned long long)ni->creation_time,
			(unsigned long long)ni->last_data_change_time,
			(unsigned long long)ni->last_mft_change_time,
			(unsigned long long)ni->last_access_time);
	ntfs_log_info("std_info ctime:%llx, mtime:%llx, mftime:%llx, atime:%llx\n",
			(unsigned long long)si_ctime, (unsigned long long)si_mtime,
			(unsigned long long)si_mtime_mft, (unsigned long long)si_atime);
	ntfs_log_info("mft_fn ctime:%llx, mtime:%llx, mftime:%llx, atime:%llx\n",
			(unsigned long long)mft_fn->creation_time,
			(unsigned long long)mft_fn->last_data_change_time,
			(unsigned long long)mft_fn->last_mft_change_time,
			(unsigned long long)mft_fn->last_access_time);
	ntfs_log_info("idx_fn ctime:%llx, mtime:%llx, mftime:%llx, atime:%llx\n",
			(unsigned long long)idx_fn->creation_time,
			(unsigned long long)idx_fn->last_data_change_time,
			(unsigned long long)idx_fn->last_mft_change_time,
			(unsigned long long)idx_fn->last_access_time);
	ntfs_log_info("======== END =======================\n");

	return;
}
#endif

/*
 * check $FILE_NAME attribute in directory index and same one in MFT entry
 * @ni : MFT entry inode
 * @ie : index entry of file (parent's index)
 * @ictx : index context for lookup, not for ni. It's context of ni's parent
 */
static int ntfsck_check_file_name_attr(ntfs_inode *ni, FILE_NAME_ATTR *ie_fn,
		ntfs_index_context *ictx)
{
	ntfs_volume *vol = ni->vol;
	char *filename;
	int ret = 0;
	BOOL need_fix = FALSE;
	FILE_NAME_ATTR *fn;
	ntfs_attr_search_ctx *actx;

	u64 idx_pdir;		/* IDX/$FN's parent MFT no */
	u64 mft_pdir;		/* MFT/$FN's parent MFT no */
	u16 idx_pdir_seq;	/* IDX/$FN's parent MFT sequence no */
	u16 mft_pdir_seq;	/* MFT/$FN's parent MFT sequence no */

	actx = ntfs_attr_get_search_ctx(ni, NULL);
	if (!actx)
		return -ENOMEM;

	filename = ntfs_attr_name_get(ie_fn->file_name, ie_fn->file_name_length);

	fn = ntfsck_find_file_name_attr(ni, ie_fn, actx);
	if (!fn) {
		/* NOT FOUND MFT/$FN */
		ntfs_log_error("Filename(%s) in INDEX ENTRY is not found in inode(%llu)\n",
				filename, (unsigned long long)ni->mft_no);
		ret = -1;
		goto out;
	}

	idx_pdir = MREF_LE(ie_fn->parent_directory);
	mft_pdir = MREF_LE(fn->parent_directory);
	idx_pdir_seq = MSEQNO_LE(ie_fn->parent_directory);
	mft_pdir_seq = MSEQNO_LE(fn->parent_directory);

#if DEBUG
	ntfsck_debug_print_fn_attr(actx, ie_fn, fn);
#endif

	/* check parent MFT reference */
	if (ie_fn->parent_directory != fn->parent_directory) {
		if (mft_pdir != ictx->ni->mft_no) {
			/* parent MFT entry is not matched! Remove this IDX/$FN */
			ntfs_log_error("Parent MFT(%llu) entry is not matched "
					"MFT/$FN's parent MFT(%llu:%s)",
					(unsigned long long)ictx->ni->mft_no,
					(unsigned long long)MREF(ie_fn->parent_directory),
					filename);
			ret = -1;
			goto out;
		}

		if (idx_pdir != mft_pdir || idx_pdir_seq != mft_pdir_seq) {
			ntfs_log_error("Parent MFT reference is differnt "
					"(IDX/$FN:%u-%llu MFT/$FN:%u-%llu) "
					"on inode(%llu, %s)",
					idx_pdir_seq, (unsigned long long)idx_pdir,
					mft_pdir_seq, (unsigned long long)mft_pdir,
					(unsigned long long)ni->mft_no, filename);
			ret = -1;
			goto out;
		}
	}

	/*
	 * Windows chkdsk seems to fix reparse tag of index entry silently.
	 * And don't touch reparse tags of MFT/$FN and $Reparse attribute.
	 */
#ifdef UNUSED
	/* check reparse point */
	if (ni->flags & FILE_ATTR_REPARSE_POINT) {
		ntfs_attr_search_ctx *_ctx = NULL;
		REPARSE_POINT *rpp = NULL;

		_ctx = ntfs_attr_get_search_ctx(ni, NULL);

		if (ntfs_attr_lookup(AT_REPARSE_POINT, AT_UNNAMED, 0,
					CASE_SENSITIVE, 0, NULL, 0, _ctx)) {
			ntfs_log_error("MFT flag set as reparse file, but there's no "
					"MFT/$REPARSE_POINT attribute on inode(%llu:%s)",
					(unsigned long long)ni->mft_no, filename);
			ntfs_attr_put_search_ctx(_ctx);
			ret = -1;
			goto out;
		}

		rpp = (REPARSE_POINT *)((u8 *)_ctx->attr +
				le16_to_cpu(_ctx->attr->value_offset));

		/* Is it worth to modify fn field? */
		if (!(fn->file_attributes & FILE_ATTR_REPARSE_POINT))
			fn->file_attributes |= FILE_ATTR_REPARSE_POINT;

		if (ie_fn->reparse_point_tag != rpp->reparse_tag) {
			check_failed("Reparse tag is different "
				"(IDX/$FN:%08lx MFT/$FN:%08lx) on inode(%llu, %s)",
				(long)le32_to_cpu(ie_fn->reparse_point_tag),
				(long)le32_to_cpu(fn->reparse_point_tag),
				(unsigned long long)ni->mft_no, filename);
			ie_fn->reparse_point_tag = rpp->reparse_tag;
			need_fix = TRUE;
			ntfs_attr_put_search_ctx(_ctx);
			goto fix_index;
		}
		ntfs_attr_put_search_ctx(_ctx);
	}
#endif

	/* Does it need to check? */

	/*
	 * mft record flags for directory is already checked
	 * in ntfsck_check_file_type()
	 */
	if (ni->mrec->flags & MFT_RECORD_IS_DIRECTORY) {
		if (!(ie_fn->file_attributes & FILE_ATTR_I30_INDEX_PRESENT)) {
			check_failed("MFT flag set as directory, but MFT/$FN flag "
					"of inode(%llu:%s) is not set!",
					(unsigned long long)ni->mft_no, filename);
			if (ntfsck_ask_repair(vol)) {
				ie_fn->file_attributes |= FILE_ATTR_I30_INDEX_PRESENT;
				fn->file_attributes = ie_fn->file_attributes;
				ntfs_index_entry_mark_dirty(ictx);
				ntfs_inode_mark_dirty(ni);
				NInoFileNameSetDirty(ni);
				fsck_err_fixed();
			}
		}

		if (ie_fn->allocated_size != 0 || ie_fn->data_size != 0 ||
				ni->allocated_size != 0 || ni->data_size != 0) {
			check_failed("Directory(%llu:%s) has non-zero "
					"length(ie:%llu,%llu, ni:%llu,%llu)",
					(unsigned long long)ni->mft_no, filename,
					(unsigned long long)ie_fn->allocated_size,
					(unsigned long long)ie_fn->data_size,
					(unsigned long long)ni->allocated_size,
					(unsigned long long)ni->data_size);
			if (ntfsck_ask_repair(vol)) {
				ni->allocated_size = 0;
				ni->data_size = 0;
				ie_fn->allocated_size = cpu_to_sle64(0);
				fn->allocated_size = ie_fn->allocated_size;
				ie_fn->data_size = cpu_to_sle64(0);
				fn->data_size = ie_fn->data_size;
				ntfs_index_entry_mark_dirty(ictx);
				ntfs_inode_mark_dirty(ni);
				NInoFileNameSetDirty(ni);
				fsck_err_fixed();
			}
		}

		/* if inode is directory, then skip size fields check */
		goto out;
	}

	/*
	 * Already applied proepr value to inode field.
	 * ni->allocated_size : $DATA->allocated_size or $DATA->compressed_size
	 */

	/* check $FN size fields */
	if (ni->allocated_size != sle64_to_cpu(ie_fn->allocated_size)) {
		check_failed("Allocated size is different "
				"(IDX/$FN:%llu MFT/$DATA:%llu) on inode(%llu, %s)",
				(unsigned long long)sle64_to_cpu(ie_fn->allocated_size),
				(unsigned long long)ni->allocated_size,
				(unsigned long long)ni->mft_no, filename);
		need_fix = TRUE;
		goto fix_index;
	}
	/*
	 * Is it need to check MFT/$FN's data size?
	 * It looks like that Windows does not check MFT/$FN's data size.
	 */
	if (ni->data_size != ie_fn->data_size) {
		check_failed("Data size is different "
				"(IDX/$FN:%llu MFT/$DATA:%llu) on inode(%llu, %s)",
				(unsigned long long)sle64_to_cpu(ie_fn->data_size),
				(unsigned long long)ni->data_size,
				(unsigned long long)ni->mft_no, filename);
		need_fix = TRUE;
		goto fix_index;
	}

	/* set NI_FileNameDirty in ni->state to sync
	 * $FILE_NAME attrib when ntfs_inode_close() is called */
fix_index:
	if (need_fix) {
		if (ntfsck_ask_repair(vol)) {
			ntfs_inode_mark_dirty(ni);
			NInoFileNameSetDirty(ni);

			ie_fn->parent_directory = fn->parent_directory;

			ie_fn->allocated_size = cpu_to_sle64(ni->allocated_size);
			ie_fn->data_size = cpu_to_sle64(ni->data_size);

			ntfs_index_entry_mark_dirty(ictx);
			fsck_err_fixed();
		}
	}

#if DEBUG
	ntfsck_debug_print_fn_attr(actx, ie_fn, fn);
#endif

out:
	ntfs_attr_name_free(&filename);
	ntfs_attr_put_search_ctx(actx);
	return ret;

}

/*
 * Find MFT/$FILE_NAME attribute that matches index entry's key.
 * Return 'fn' if found, else return NULL.
 *
 * 'fn' points somewhere in 'actx->attr', so 'fn' is only valid
 * during 'actx' variable is valid. (ie. before calling
 * ntfs_attr_put_search_ctx() * or ntfs_attr_reinit_search_ctx()
 * outside of this function)
 */
static FILE_NAME_ATTR *ntfsck_find_file_name_attr(ntfs_inode *ni,
		FILE_NAME_ATTR *ie_fn, ntfs_attr_search_ctx *actx)
{
	FILE_NAME_ATTR *fn = NULL;
	ATTR_RECORD *attr;
	ntfs_volume *vol = ni->vol;
	int ret;

#ifdef DEBUG
	char *filename;
	char *idx_filename;

	idx_filename = ntfs_attr_name_get(ie_fn->file_name, ie_fn->file_name_length);
	ntfs_log_trace("Find '%s' matched $FILE_NAME attribute\n", idx_filename);
	ntfs_attr_name_free(&idx_filename);
#endif

	while ((ret = ntfs_attr_lookup(AT_FILE_NAME, AT_UNNAMED, 0, CASE_SENSITIVE,
					0, NULL, 0, actx)) == 0) {
		IGNORE_CASE_BOOL case_sensitive = IGNORE_CASE;

		attr = actx->attr;
		fn = (FILE_NAME_ATTR *)((u8 *)attr +
				le16_to_cpu(attr->value_offset));
#ifdef DEBUG
		filename = ntfs_attr_name_get(fn->file_name, fn->file_name_length);
		ntfs_log_trace("  name:'%s' type:%d\n", filename, fn->file_name_type);
		ntfs_attr_name_free(&filename);
#endif

		if (fn->file_name_type == FILE_NAME_POSIX)
			case_sensitive = CASE_SENSITIVE;

		if (!ntfs_names_are_equal(fn->file_name, fn->file_name_length,
					ie_fn->file_name, ie_fn->file_name_length,
					case_sensitive, vol->upcase,
					vol->upcase_len)) {
			continue;
		}

		/* Found $FILE_NAME */
		return fn;
	}

	return NULL;
}

/*
 * check file is normal file or directory.
 * and check flags related it.
 *
 * return index entry's flag if checked normally.
 * else return -1.
 *
 */
static int32_t ntfsck_check_file_type(ntfs_inode *ni, ntfs_index_context *ictx,
		FILE_NAME_ATTR *ie_fn)
{
	FILE_ATTR_FLAGS ie_flags; /* index key $FILE_NAME flags */
	ntfs_volume *vol = ni->vol;
	BOOL check_ir = FALSE;	/* flag about checking index root */

	ie_flags = ie_fn->file_attributes;

	if (ni->mrec->flags & MFT_RECORD_IS_DIRECTORY) {
		/* mft record flags is set to directory */
		if (ntfs_attr_exist(ni, AT_INDEX_ROOT, NTFS_INDEX_I30, 4)) {
			if (!(ie_flags & FILE_ATTR_I30_INDEX_PRESENT)) {
				check_failed("MFT(%llu) flag is set to directory, "
						"but Index/$FILE_NAME is not set.",
						(unsigned long long)ni->mft_no);
				ie_flags |= FILE_ATTR_I30_INDEX_PRESENT;
				ie_fn->file_attributes |= FILE_ATTR_I30_INDEX_PRESENT;
				if (ntfsck_ask_repair(vol)) {
					ntfs_index_entry_mark_dirty(ictx);
					fsck_err_fixed();
				}
			}
		} else {
#ifndef UNUSED
			/* return if flags set directory, but not exist $IR */
			return STATUS_ERROR;
#else
			if (errno != ENOENT)
				return STATUS_ERROR;

			/* not found $INDEX_ROOT, check failed */
			check_failed("MFT(%llu) flag is set to directory, "
					"but there's no MFT/$IR attr.",
					(unsigned long long)ni->mft_no);
			ie_flags &= ~FILE_ATTR_I30_INDEX_PRESENT;
			ni->mrec->flags &= ~MFT_RECORD_IS_DIRECTORY;
			if (ntfsck_ask_repair(vol)) {
				ntfs_inode_mark_dirty(ni);
				fsck_err_fixed();
			}

			if (ie_flags & FILE_ATTR_I30_INDEX_PRESENT) {
				check_failed("MFT(%llu) $IR does not exist, "
						"but Index/$FILE_NAME flag is set to "
						"directory.",
						(unsigned long long)ni->mft_no);
				ie_flags &= ~FILE_ATTR_I30_INDEX_PRESENT;
				ie_fn->file_attributes &= ~FILE_ATTR_I30_INDEX_PRESENT;
				if (ntfsck_ask_repair(vol)) {
					ntfs_index_entry_mark_dirty(ictx);
					fsck_err_fixed();
				}
			}
#endif
		}
		check_ir = TRUE;
	}

	if (!(ni->mrec->flags & MFT_RECORD_IS_DIRECTORY)) {
		/* mft record flags is not set to directory */
		if (ntfs_attr_exist(ni, AT_DATA, AT_UNNAMED, 0)) {
			if (ie_flags & FILE_ATTR_I30_INDEX_PRESENT) {
				check_failed("MFT(%llu) flag is set to file, "
						"but MFT/$IR is set to directory.",
						(unsigned long long)ni->mft_no);
				ie_flags &= ~FILE_ATTR_I30_INDEX_PRESENT;
				ie_fn->file_attributes &= ~FILE_ATTR_I30_INDEX_PRESENT;
				if (ntfsck_ask_repair(vol)) {
					ntfs_index_entry_mark_dirty(ictx);
					fsck_err_fixed();
				}
			}
		} else {
			if (check_ir == TRUE) {
				/*
				 * Already checked index root attr.
				 * It means there are no $INDEX_ROOT and
				 * $DATA in inode.
				 */
				return STATUS_ERROR;
			}
			if (!ntfs_attr_exist(ni, AT_INDEX_ROOT, NTFS_INDEX_I30, 4)) {
				/* there are no $DATA and $INDEX_ROOT in MFT */
				return STATUS_ERROR;
			}

			check_failed("MFT(%llu) flag is set to file, "
					"but there's no MFT/$DATA, but MFT/$IR.",
					(unsigned long long)ni->mft_no);
			/* found $INDEX_ROOT */
			ie_flags |= FILE_ATTR_I30_INDEX_PRESENT;
			ie_fn->file_attributes |= FILE_ATTR_I30_INDEX_PRESENT;
			if (ntfsck_ask_repair(vol)) {
				ntfs_index_entry_mark_dirty(ictx);
				fsck_err_fixed();
			}
		}
	}
	return (int32_t)ie_flags;
}

/*
 * Decompose non-resident cluster run and make into runlist.
 *
 * If cluster run should be repaired, need_fix will be set to TRUE.
 * Even if cluster runs is corrupted, runlist array will preserve
 * healthy state data even after encountering corruption.
 *
 * If error occur during decompose cluster run, next found attributes
 * will be deleted.(In case there are multiple identical attribute exist)
 * Before deleting attribute, rl will have deleleted attribute's cluster run
 * information.(lcn field of rl which error occurred, may be LCN_ENOENT
 * or LCN_RL_NOT_MAPPED)
 *
 * If attribute is resident, it will be deleted. So caller should check
 * that only non-resident attribute will be passed to this function.
 *
 * rl may have normal cluster run information or deleted information
 * Return runlist array(rl) if success.
 * If caller need to apply modified runlist, then *need_fix is set to TRUE.
 *
 * Return NULL if it failed to make runlist noramlly.
 * need_fix value is valid only when return success.
 */

/* TODO: move this to runlist.c ? */
static runlist_element *ntfsck_decompose_mp(ntfs_attr *na, BOOL *need_fix)
{
	ntfs_volume *vol;
	ntfs_inode *ni;
	runlist *rl = NULL;
	runlist *part_rl = NULL;
	VCN next_vcn, last_vcn, highest_vcn;
	ATTR_RECORD *attr = NULL;
	ntfs_attr_search_ctx *actx;

	if (!na || !na->ni) {
		errno = EINVAL;
		return NULL;
	}
	ni = na->ni;
	vol = ni->vol;

	actx = ntfs_attr_get_search_ctx(ni, NULL);
	if (!actx) {
		errno = ENOMEM;
		return NULL;
	}

	next_vcn = last_vcn = highest_vcn = 0;
	/* There can be multiple $INDEX_ALLOCATION attributes in a inode */
	while (1) {
		runlist *temp_rl = NULL;

		if (ntfs_attr_lookup(na->type, na->name, na->name_len, CASE_SENSITIVE,
					next_vcn, NULL, 0, actx)) {
			errno = ENOENT;
			break;
		}

		attr = actx->attr;

		/* remove resident attribute */
		if (!attr->non_resident) {
			check_failed("Inode(%llu)'s attribute(%d) has resident "
					"type, remove it",
					(unsigned long long)ni->mft_no, attr->type);
			if (ntfsck_ask_repair(vol)) {
				if (ntfs_attr_record_rm(actx)) {
					ntfs_log_error("Couldn't remove attribute(%llu:%d).\n",
							(unsigned long long)ni->mft_no,
							attr->type);
				}
				fsck_err_fixed();
			}
			continue;
		}

		temp_rl = rl;
		rl = ntfs_mapping_pairs_decompress_on_fsck(vol, attr, temp_rl,
				&part_rl);
		if (!rl) {
			/*
			 * decompress mp failed,
			 * but part of mp is preserved in part_rl.
			 */

			if (!part_rl) {
				part_rl = ntfs_calloc(sizeof(runlist));
				if (!part_rl)
					goto out;
				part_rl->vcn = 0;
				part_rl->lcn = LCN_ENOENT;
				part_rl->length = 0;
			}

			rl = part_rl;
			*need_fix = TRUE;
			/*
			 * In case of decompress mp failure, fsck will
			 * truncate it to zero size.
			 * That is same as Windows repairing tool.
			 */
		} else {
			/* remove found attribute after error occurred. */
			if (*need_fix == TRUE) {
				check_failed("Found corrupted mapping pairs array of inode(%llu). "
						"Fix it", (unsigned long long)ni->mft_no);
				if (ntfsck_ask_repair(vol)) {
					if (ntfs_attr_record_rm(actx)) {
						ntfs_log_error("Couldn't remove attribute(%llu:%d).\n",
								(unsigned long long)ni->mft_no,
								attr->type);
					}
					fsck_err_fixed();
					continue;
				}
			}
		}

		/* first $IA attribute */
		if (!next_vcn) {
			if (attr->lowest_vcn) {
				check_failed("inode(%llu)'s first $DATA"
						" lowest_vcn is not zero",
						(unsigned long long)ni->mft_no);
				errno = EIO;
				/* should fix attribute's lowest_vcn */
				if (ntfsck_ask_repair(vol)) {
					attr->lowest_vcn = 0;
					NInoSetDirty(ni);
					fsck_err_fixed();
				}
				break;
			}
		}

		highest_vcn = sle64_to_cpu(attr->highest_vcn);
		next_vcn = highest_vcn + 1;

		if (next_vcn <= 0) {
			errno = ENOENT;
			break;
		}

		/* Avoid endless loops due to corruption */
		if (next_vcn < sle64_to_cpu(attr->lowest_vcn)) {
			ntfs_log_error("Inode %llu has corrupt attribute list\n",
					(unsigned long long)ni->mft_no);
			/* TODO: how attribute list repair ?? */
			errno = EIO;
			break;
		}
	}

out:
	ntfs_attr_put_search_ctx(actx);
	return rl;
}

/*
 * Remove $IA/$BITMAP, and initialize $IR attribute for repairing.
 * This function should be called $IA or $BITMAP attribute is corrupted.
 */
static int ntfsck_initialize_index_attr(ntfs_inode *ni)
{
	ntfs_attr *bm_na = NULL;
	ntfs_attr *ia_na = NULL;
	ntfs_attr *ir_na = NULL;
	u8 bmp[8];
	int ret = STATUS_ERROR;

	/*
	 * Remove both ia attr and bitmap attr and recreate them.
	 */
	ia_na = ntfs_attr_open(ni, AT_INDEX_ALLOCATION, NTFS_INDEX_I30, 4);
	if (ia_na) {
		if (ntfs_attr_rm(ia_na)) {
			ntfs_log_error("Failed to remove $IA attr. of inode(%lld)\n",
					(unsigned long long)ni->mft_no);
			goto out;
		}
		ntfs_attr_close(ia_na);
		ia_na = NULL;
	}

	bm_na = ntfs_attr_open(ni, AT_BITMAP, NTFS_INDEX_I30, 4);
	if (bm_na) {
		if (ntfs_attr_rm(bm_na)) {
			ntfs_log_error("Failed to remove $BITMAP attr. of "
					" inode(%lld)\n",
					(unsigned long long)ni->mft_no);
			goto out;
		}
		ntfs_attr_close(bm_na);
		bm_na = NULL;
	}

	ir_na = ntfs_attr_open(ni, AT_INDEX_ROOT, NTFS_INDEX_I30, 4);
	if (!ir_na) {
		ntfs_log_verbose("Can't open $IR attribute from mft(%ld) entry\n",
				ni->mft_no);
		goto out;
	}

	ret = ntfs_attr_truncate(ir_na,
			sizeof(INDEX_ROOT) + sizeof(INDEX_ENTRY_HEADER));
	if (ret == STATUS_OK) {
		INDEX_ROOT *ir;
		INDEX_ENTRY *ie;
		int index_len =
			sizeof(INDEX_HEADER) + sizeof(INDEX_ENTRY_HEADER);

		ir = ntfs_ir_lookup2(ni, NTFS_INDEX_I30, 4);
		if (!ir)
			goto out;

		ir->index.allocated_size = cpu_to_le32(index_len);
		ir->index.index_length = cpu_to_le32(index_len);
		ir->index.entries_offset = const_cpu_to_le32(sizeof(INDEX_HEADER));
		ir->index.ih_flags = SMALL_INDEX;
		ie = (INDEX_ENTRY *)((u8 *)ir + sizeof(INDEX_ROOT));
		ie->length = cpu_to_le16(sizeof(INDEX_ENTRY_HEADER));
		ie->key_length = 0;
		ie->ie_flags = INDEX_ENTRY_END;
	} else if (ret == STATUS_ERROR) {
		ntfs_log_perror("Failed to truncate INDEX_ROOT");
		goto out;
	}

	ntfs_attr_close(ir_na);
	ir_na = NULL;

	ret = STATUS_ERROR;	/* initialize return code */

	/*
	 * Recreate both $BITMAP attr and $IA attr.
	 * All entries in this directory will be
	 * orphaned and they will be revived when
	 * checking orphaned entries under parse.
	 */
	memset(bmp, 0, sizeof(bmp));
	if (ntfs_attr_add(ni, AT_BITMAP, NTFS_INDEX_I30, 4,
				bmp, sizeof(bmp))) {
		ntfs_log_perror("Failed to add AT_BITMAP");
		goto out;
	}

	if (ntfs_attr_add(ni, AT_INDEX_ALLOCATION, NTFS_INDEX_I30, 4,
				NULL, 0)) {
		ntfs_log_perror("Failed to add AT_INDEX_ALLOCATION");
		goto out;
	}
	ntfs_inode_mark_dirty(ni);

	ret = STATUS_OK;
out:
	if (ir_na)
		ntfs_attr_close(ir_na);
	if (ia_na)
		ntfs_attr_close(ia_na);
	if (bm_na)
		ntfs_attr_close(bm_na);
	return ret;
}

/*
 * Read from disk of non-resident attribute's cluster run,
 * and make rl structure. Even if error occurred during decomposing
 * runlist, * rl will include only valid cluster run of attribute.
 *
 * And rl also has another valid cluster run of next attribute.
 * (multiple same name attribute may exist)
 *
 * If error occurred during decomposing runlist, lcn field of rl may
 * have LCN_RL_NOT_MAPPED or not. So
 */
static int ntfsck_check_attr_runlist(ntfs_attr *na, struct rl_size *rls,
		BOOL *need_fix)
{
	runlist *rl = NULL;
	int ret = STATUS_OK;

	rl = ntfsck_decompose_mp(na, need_fix);
	if (!rl) {
		ntfs_log_error("Failed to get $IA "
				"attribute in directory(%lld)",
				(unsigned long long)na->ni->mft_no);
		return STATUS_ERROR;
	}

#ifdef _DEBUG
	ntfs_log_info("Before =========================\n");
	ntfs_dump_runlist(rl);
#endif

	na->rl = rl;

	ret = ntfsck_setbit_runlist(na->ni, na->rl, 1, rls);
	if (ret)
		return STATUS_ERROR;

#ifdef _DEBUG
	ntfs_log_info("After =========================\n");
	ntfs_dump_runlist(rl);
#endif
	return 0;
}

static int ntfsck_truncate_attr(ntfs_attr *na, s64 new_size)
{
	na->allocated_size = new_size;

	/* apply rl to disk */
	NAttrSetFullyMapped(na);
	if (ntfs_attr_update_mapping_pairs(na, 0)) {
		ntfs_log_error("Failed to update mapping pairs of "
				"inode(%llu)\n",
				(unsigned long long)na->ni->mft_no);
		return -1;
	}

	if (ntfs_attr_truncate(na, na->allocated_size)) {
		ntfs_log_error("Failed to truncate file\n");
		return -1;
	}
	return 0;
}

static int ntfsck_check_directory(ntfs_inode *ni)
{
	ntfs_volume *vol;
	ntfs_attr *ia_na = NULL;
	ntfs_attr *bm_na = NULL;
	BOOL need_fix = FALSE;
	struct rl_size rls = {0, };
	int ret = STATUS_OK;

	if (!ni)
		return -EINVAL;

	vol = ni->vol;

	/*
	 * header size and overflow is already checked in opening inode
	 * (ntfs_attr_inconsistent()). just check existence of $INDEX_ROOT.
	 */
	if (!ntfs_attr_exist(ni, AT_INDEX_ROOT, NTFS_INDEX_I30, 4)) {
		ntfs_log_perror("$IR is missing in inode(%lld)",
				(unsigned long long)ni->mft_no);
		ret = STATUS_ERROR;
		/* remove mft entry */
		goto out;
	}

	ia_na = ntfs_attr_open(ni, AT_INDEX_ALLOCATION, NTFS_INDEX_I30, 4);
	if (!ia_na) {
		/* directory can have only $INDEX_ROOT. not error */

		/* check $BITMAP if exist */
		bm_na = ntfs_attr_open(ni, AT_BITMAP, NTFS_INDEX_I30, 4);
		if (!bm_na) {
			/* both $IA and $BITMAP do not exist. it's OK. */
			ret = STATUS_OK;
			goto check_next;
		}

		/* only $BITMAP exist, remove it */
		if (ntfs_attr_rm(bm_na)) {
			ntfs_log_error("Failed to remove $BITMAP attr. of "
					" inode(%lld)\n",
					(unsigned long long)ni->mft_no);
			ret = STATUS_ERROR;
			goto out;
		}
		ntfs_attr_close(bm_na);
		bm_na = NULL;
		goto check_next;
	}

	/* $INDEX_ALLOCATION is always non-resident */
	if (!NAttrNonResident(ia_na)) {
		/* TODO: check $BITMAP, if exist, remove bitmap and ia */
		ret = STATUS_ERROR;
		goto init_all;
	}

	/* check $IA cluster run */
	if (ntfsck_check_attr_runlist(ia_na, &rls, &need_fix)) {
		check_failed("Failed to get $BITMAP "
				"attribute in directory(%lld)",
				(unsigned long long)ni->mft_no);
		goto init_all;
	}

	/* if need_fix is set to TRUE, apply modified runlist to cluster runs */
	if (need_fix == TRUE) {
		check_failed("$IA cluster run of inode(%lld) "
				"corrupted. truncate it",
				(unsigned long long)ni->mft_no);

		if (ntfsck_ask_repair(vol)) {
			s64 tr_size;

			/*
			 * keep a valid runlist as long as possible.
			 * if truncate zero, call with second parameter to 0
			 */
			tr_size = rls.vcn << vol->cluster_size_bits;
			if (ntfsck_truncate_attr(ia_na, tr_size))
				goto init_all;

			fsck_err_fixed();
		}
	}

	ntfs_attr_close(ia_na);
	ia_na = NULL;

	/*
	 * check $BITMAP's cluster run
	 * TODO: is it possible multiple $BITMAP attrib in inode?
	 */
	bm_na = ntfs_attr_open(ni, AT_BITMAP, NTFS_INDEX_I30, 4);
	if (!bm_na) {
		u8 bmp[8];

		ntfs_log_perror("Failed to open $BITMAP of inode %llu",
				(unsigned long long)ni->mft_no);

		memset(bmp, 0, sizeof(bmp));
		if (ntfs_attr_add(ni, AT_BITMAP, NTFS_INDEX_I30, 4, bmp,
					sizeof(bmp))) {
			ntfs_log_perror("Failed to add AT_BITMAP");
			ret = STATUS_ERROR;
			goto out;
		}
	}

	if (NAttrNonResident(bm_na)) {
		memset(&rls, 0, sizeof(struct rl_size));
		need_fix = FALSE;

		if (ntfsck_check_attr_runlist(bm_na, &rls, &need_fix)) {
			check_failed("Failed to get $BITMAP cluster run in "
					"inode(%lld)",
					(unsigned long long)ni->mft_no);
			goto init_all;
		}

		/* if need_fix is set to TRUE, apply modified runlist to cluster runs */
		if (need_fix == TRUE) {
			check_failed("$BITMAP cluster run of inode(%lld) "
					"corrupted. truncate it",
					(unsigned long long)ni->mft_no);

			if (ntfsck_ask_repair(vol)) {
				s64 tr_size = 0;

				/*
				 * keep a valid runlist as long as possible.
				 * if truncate zero, call with second parameter to 0
				 */
				tr_size = rls.vcn << vol->cluster_size_bits;
				if (ntfsck_truncate_attr(bm_na, tr_size))
					goto init_all;

				fsck_err_fixed();
			}
		}
	}

check_next:
	/* TODO: need to check flag & size in na ? */
	/* TODO: other checking ? */

out:
	if (bm_na)
		ntfs_attr_close(bm_na);
	if (ia_na)
		ntfs_attr_close(ia_na);

	return ret;

init_all:
	if (bm_na)
		ntfs_attr_close(bm_na);
	if (ia_na)
		ntfs_attr_close(ia_na);

	ntfsck_initialize_index_attr(ni);
	fsck_err_fixed();
	return ret;
}

static int ntfsck_check_file(ntfs_inode *ni)
{
	ntfs_volume *vol;
	ntfs_attr *na = NULL;
	FILE_ATTR_FLAGS si_flags; /* $STANDARD_INFORMATION flags */
	BOOL need_fix = FALSE;
	struct rl_size rls = {0, };
	int ret = 0;

	if (!ni)
		return -1;

	vol = ni->vol;

	na = ntfs_attr_open(ni, AT_DATA, AT_UNNAMED, 0);
	if (!na) {
		ntfs_log_perror("Failed to open $DATA of inode "
				"%llu", (unsigned long long)ni->mft_no);
		return -1;
	}

	if (NAttrNonResident(na)) {
		if (ntfsck_check_attr_runlist(na, &rls, &need_fix)) {
			ntfs_log_error("Failed to get $DATA "
					"attribute in file(%lld)",
					(unsigned long long)ni->mft_no);
			ret = -1;
			goto attr_close;
		}

		/*
		 * if need_fix is set to TRUE,
		 * apply modified runlist to cluster runs.
		 */
		if (need_fix == TRUE) {
			check_failed("$DATA cluster run of inode(%lld) "
					"corrupted. truncate it",
					(unsigned long long)ni->mft_no);

			if (ntfsck_ask_repair(vol)) {
				s64 tr_size;

				/* truncate with calculated size of repaired cluster run */
				tr_size = rls.vcn << vol->cluster_size_bits;
				if (ntfsck_truncate_attr(na, tr_size)) {
					ntfs_log_info("truncate attr failed\n");
					goto attr_close;
				}

				ni->allocated_size = na->allocated_size;
				ni->data_size = na->data_size;
				ntfs_inode_mark_dirty(ni);
				fsck_err_fixed();
			}
			goto attr_close;
		}

	} else {
		rls.asize = na->data_size;
		rls.real_asize = na->allocated_size;
	}

	si_flags = ni->flags;

	/* check sparse/compressed file */
	if (rls.real_asize != ((rls.asize + 7) & ~7)) {
		/* check flags */
		/* can't recognize SPARSE/COMPRESSED FILE using cluster run */
		if (!(si_flags & (FILE_ATTR_SPARSE_FILE | FILE_ATTR_COMPRESSED)) ||
			!(na->data_flags & (ATTR_IS_SPARSE | ATTR_IS_COMPRESSED))) {
			check_failed("inode(%llu)'s $STD_INFO flag(%d) $DATA flag(%d)"
					" does not set SPARSE or COMPRESSED",
					(unsigned long long)ni->mft_no,
					si_flags, na->data_flags);

			/* if comression_block_size is not zero, attribute is comressed */
			if (ntfsck_ask_repair(vol)) {
				if (na->compression_block_size) {
					si_flags &= ~FILE_ATTR_SPARSE_FILE;
					ni->flags = si_flags |= FILE_ATTR_COMPRESSED;
					na->data_flags &= ~ATTR_IS_SPARSE;
					na->data_flags |= ATTR_IS_COMPRESSED;
				} else {
					si_flags &= ~FILE_ATTR_COMPRESSED;
					ni->flags = si_flags |= FILE_ATTR_SPARSE_FILE;
					na->data_flags &= ~ATTR_IS_COMPRESSED;
					na->data_flags |= ATTR_IS_SPARSE;
				}
				ntfs_inode_mark_dirty(ni);
				NInoFileNameSetDirty(ni);
				fsck_err_fixed();
			}
		}

		/* check size */
		if ((ni->allocated_size != na->compressed_size) ||
				(na->compressed_size != rls.real_asize)) {
			/* need to set allocated_size & highest_vcn set */
			check_failed("Corrupted inode(%llu) compressed size field.\n "
					" inode allocated size(%llu),"
					" $DATA compressed(%llu)"
					" cluster run real allocation(%llu).",
					(unsigned long long)ni->mft_no,
					(unsigned long long)ni->allocated_size,
					(unsigned long long)na->compressed_size,
					(unsigned long long)rls.real_asize);
			if (ntfsck_ask_repair(vol)) {
				na->compressed_size = rls.real_asize;
				ni->allocated_size = na->compressed_size;
				ntfs_inode_mark_dirty(ni);
				NInoFileNameSetDirty(ni);
				fsck_err_fixed();
			}
		}
	} else {
		if ((si_flags & (FILE_ATTR_SPARSE_FILE | FILE_ATTR_COMPRESSED)) ||
			(na->data_flags & (ATTR_IS_SPARSE | ATTR_IS_COMPRESSED))) {
			check_failed("inode(%llu)'s $STD_INFO flag(%d) $DATA flag(%d)"
					" set SPARSE or COMPRESSED",
					(unsigned long long)ni->mft_no,
					si_flags, na->data_flags);

			/* if comression_block_size is not zero, attribute is comressed */
			if (ntfsck_ask_repair(vol)) {
				si_flags &= ~(FILE_ATTR_COMPRESSED | FILE_ATTR_SPARSE_FILE);
				ni->flags = si_flags;
				na->data_flags &= ~(ATTR_IS_COMPRESSED | ATTR_IS_SPARSE);

				ntfs_inode_mark_dirty(ni);
				NInoFileNameSetDirty(ni);
				fsck_err_fixed();
			}
		}


		/* check size */
		if ((ni->allocated_size != na->allocated_size) ||
				(na->allocated_size != rls.real_asize)) {
			check_failed("Corrupted inode(%llu) allocated size field.\n "
					" inode allocated size(%llu),"
					" $DATA allocated(%llu),"
					" cluster run(total(%llu):real(%llu) allocation.",
					(unsigned long long)ni->mft_no,
					(unsigned long long)ni->allocated_size,
					(unsigned long long)na->allocated_size,
					(unsigned long long)rls.asize,
					(unsigned long long)rls.real_asize);
			if (ntfsck_ask_repair(vol)) {
				na->allocated_size = rls.real_asize;
				ni->allocated_size = na->allocated_size;
				ntfs_inode_mark_dirty(ni);
				NInoFileNameSetDirty(ni);
				fsck_err_fixed();
			}
		}
	}

attr_close:
	/*
	 * if rl is allocated in ntfsck_decompose_mp(),
	 * will be freed in ntfs_attr_close()
	 */
	ntfs_attr_close(na);
	return ret;
}

/* called after ntfs_inode_attatch_all_extents() is called */
static int ntfsck_set_mft_record_bitmap(ntfs_inode *ni)
{
	int ext_idx = 0;

	if (!ni)
		return STATUS_ERROR;

	if (ntfsck_mft_bmp_bit_set(ni->mft_no)) {
		ntfs_log_error("Failed to set MFT bitmap for (%llu)\n",
				(unsigned long long)ni->mft_no);
		/* do not return error */
	}

	/* set mft record bitmap */
	while (ext_idx < ni->nr_extents) {
		if (ntfsck_mft_bmp_bit_set(ni->extent_nis[ext_idx]->mft_no)) {
			/* do not return error */
			break;
		}
		ext_idx++;
	}
	return STATUS_OK;
}

static int ntfsck_check_inode(ntfs_inode *ni, INDEX_ENTRY *ie,
		ntfs_index_context *ictx)
{
	FILE_NAME_ATTR *ie_fn = (FILE_NAME_ATTR *)&ie->key.file_name;
	int32_t flags;
	int ret;

	ntfs_inode_attach_all_extents(ni);

	/* Check file type */
	flags = ntfsck_check_file_type(ni, ictx, ie_fn);
	if (flags < 0)
		goto remove_index;

	if (flags & FILE_ATTR_I30_INDEX_PRESENT) {
		ret = ntfsck_check_directory(ni);
		if (ret)
			goto remove_index;
	} else {
		ret = ntfsck_check_file(ni);
		if (ret)
			goto remove_index;
	}

	/* check $FILE_NAME */
	ret = ntfsck_check_file_name_attr(ni, ie_fn, ictx);
	if (ret < 0)
		goto remove_index;

	ntfsck_set_mft_record_bitmap(ni);
	return STATUS_OK;

remove_index:
	return STATUS_ERROR;

}

static int ntfsck_add_dir_list(ntfs_volume *vol, INDEX_ENTRY *ie,
			       ntfs_index_context *ictx)
{
	char *filename;
	ntfs_inode *ni;
	struct dir *dir;
	MFT_REF mref;
	int ret = 0;
	FILE_NAME_ATTR *ie_fn = &ie->key.file_name;

	if (!ie)
		return -1;

	mref = le64_to_cpu(ie->indexed_file);
	if (MREF(mref) == FILE_root)
		return 0;

	filename = ntfs_attr_name_get(ie_fn->file_name, ie_fn->file_name_length);
	ntfs_log_verbose("ntfsck_check_index %ld, %s\n", MREF(mref), filename);

	ni = ntfs_inode_open(vol, MREF(mref));
	if (ni) {
		/* skip checking for system files */
		if (!(ni->flags & FILE_ATTR_SYSTEM)) {
			ret = ntfsck_check_inode(ni, ie, ictx);
			if (ret) {
				ntfs_log_info("ntfsck_check_inode(%llu) failed\n",
						(unsigned long long)ni->mft_no);

				ntfs_inode_close(ni);
				goto remove_index;
			}
		} else {
			/* for inode whose parent inode is system files */
			ntfsck_set_mft_record_bitmap(ni);
		}

		if ((ie->key.file_name.file_attributes & FILE_ATTR_I30_INDEX_PRESENT) &&
				strcmp(filename, ".")) {
			dir = (struct dir *)calloc(1, sizeof(struct dir));
			if (!dir) {
				ntfs_log_error("Failed to allocate for subdir.\n");
				ret = -1;
				ntfs_inode_close(ni);
				goto err_out;
			}

			dir->ni = ni;
			ntfs_list_add_tail(&dir->list, &ntfs_dirs_list);
		} else {
			ntfs_inode_close_in_dir(ni, ictx->ni);
		}
	} else {

remove_index:
		check_failed("mft entry(%llu:%s) is corrupted, Removing index entry(%llu)",
				(unsigned long long)MREF(mref), filename,
				(unsigned long long)MREF_LE(ie_fn->parent_directory));
		if (ntfsck_ask_repair(vol)) {
			ictx->entry = ie;
			ret = ntfs_index_rm(ictx);
			if (ret) {
				ntfs_log_error("Failed to remove index entry of inode(%llu:%s)\n",
						(unsigned long long)MREF(mref), filename);
			} else {
				ntfs_log_verbose("Index entry of inode(%llu:%s) is deleted\n",
						(unsigned long long)MREF(mref), filename);
				ret = 1;
				fsck_err_fixed();
			}
			ntfs_inode_mark_dirty(ictx->actx->ntfs_ino);
		}
	}

err_out:
	free(filename);
	return ret;
}

static int ntfsck_scan_index_entries_btree(ntfs_volume *vol)
{
	ntfs_inode *ni;
	struct dir *dir;
	INDEX_ROOT *ir;
	INDEX_ENTRY *next;
	INDEX_ENTRY *prev;
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

	if (ntfsck_check_directory(ni)) {
		ntfs_log_error("Root directory has corrupted.\n");
		exit(-1);
	}

	dir->ni = ni;
	ntfs_list_add(&dir->list, &ntfs_dirs_list);

	while (!ntfs_list_empty(&ntfs_dirs_list)) {
		dir = ntfs_list_entry(ntfs_dirs_list.next, struct dir, list);

		ctx = ntfs_attr_get_search_ctx(dir->ni, NULL);
		if (!ctx)
			goto err_continue;

		/* Find the index root attribute in the mft record. */
		if (ntfs_attr_lookup(AT_INDEX_ROOT, NTFS_INDEX_I30, 4, CASE_SENSITIVE, 0, NULL,
					0, ctx)) {
			ntfs_log_perror("Index root attribute missing in directory inode "
					"%lld", (unsigned long long)dir->ni->mft_no);
			ntfs_attr_put_search_ctx(ctx);
			goto err_continue;
		}

		/* Get to the index root value. */
		ir = (INDEX_ROOT*)((u8*)ctx->attr +
				le16_to_cpu(ctx->attr->value_offset));

		cr = ir->collation_rule;

		ictx = ntfs_index_ctx_get(dir->ni, NTFS_INDEX_I30, 4);
		if (!ictx) {
			ntfs_attr_put_search_ctx(ctx);
			goto err_continue;
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
			goto err_continue;
		}

		if (vol->cluster_size <= ictx->block_size)
			ictx->vcn_size_bits = vol->cluster_size_bits;
		else
			ictx->vcn_size_bits = NTFS_BLOCK_SIZE_BITS;

		/* The first index entry. */
		next = (INDEX_ENTRY*)((u8*)&ir->index +
				le32_to_cpu(ir->index.entries_offset));

		if (next->ie_flags & INDEX_ENTRY_NODE) {
			ictx->ia_na = ntfs_attr_open(dir->ni, AT_INDEX_ALLOCATION,
						    ictx->name, ictx->name_len);
			if (!ictx->ia_na) {
				ntfs_log_perror("Failed to open index allocation of inode "
						"%llu", (unsigned long long)dir->ni->mft_no);
				goto err_continue;
			}
		}
		prev = next;

		ret = ntfs_index_entry_inconsistent(vol, next, cr, 0, ictx);
		if (ret > 0) {
			ret = ntfsck_update_index_entry(ictx);
			if (ret) {
				fsck_err_failed();
				goto err_continue;
			}
			prev = next;
		}

		if (next->ie_flags & INDEX_ENTRY_NODE) {
			next = ntfs_index_walk_down(next, ictx);
			if (!next)
				goto next_dir;
		}

		if (!(next->ie_flags & INDEX_ENTRY_END))
			goto add_dir_list;

		while ((next = ntfs_index_next(next, ictx)) != NULL) {
add_dir_list:
			prev = next;
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
		if (!next && ictx->bad_index == TRUE) {
			INDEX_ENTRY *ie_temp;
			INDEX_HEADER *ih;

			check_failed("Index block is corrupted. inode(%llu)",
					(unsigned long long)dir->ni->mft_no);

			if (ntfsck_ask_repair(vol)) {
				ictx->entry = prev;	/* set previous entry */
				prev->ie_flags &= ~INDEX_ENTRY_NODE;
				prev->length = cpu_to_le16(le16_to_cpu(prev->length) - 8);

				/* ntfs_ie_end() */
				if (prev->ie_flags & INDEX_ENTRY_END || !prev->length) {
					if (ictx->parent_vcn[ictx->pindex] == VCN_INDEX_ROOT_PARENT) {
						ih = &ictx->ir->index;
						if (ntfs_ih_zero_entry(ih)) {
							ntfs_attr_truncate(ictx->ia_na, 0);
							ih->ih_flags = SMALL_INDEX;
						}
					}
				} else {
					/* TODO: set flags */
					ie_temp = ntfs_ie_dup_novcn(prev);
					ret = ntfs_index_rm(ictx);
					ntfs_ie_add(ictx, ie_temp);
					free(ie_temp);
				}

				if (ictx->parent_vcn[ictx->pindex] == VCN_INDEX_ROOT_PARENT)
					ntfs_inode_mark_dirty(ictx->actx->ntfs_ino);
				else
					if (ntfs_ib_write(ictx, ictx->prev_ib))
						goto err_continue;

				/* set ictx field to free in ntfs_index_ctx_put() */
				ictx->entry = NULL;
				ictx->bad_index = FALSE;

				if (ictx->prev_ib && ictx->prev_ib != ictx->ib)
					free(ictx->prev_ib);

				ictx->prev_ib = NULL;
				fsck_err_fixed();
			}
		}
err_continue:
		if (ictx) {
			ntfs_inode_mark_dirty(ictx->actx->ntfs_ino);
			ntfs_index_ctx_put(ictx);
			ictx = NULL;
		}
		ntfs_inode_close(dir->ni);
		ntfs_list_del(&dir->list);
		free(dir);
	}

	return 0;
}

static int ntfsck_scan_index_entries(ntfs_volume *vol)
{
	ntfs_log_info("Parse #%d: Check index entries in volume...\n", parse_count++);

	return ntfsck_scan_index_entries_btree(vol);
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
		check_failed("ntfs logfile reset failed, errno : %d\n", errno);
		return -1;
	}

	return 0;
}

static ntfs_volume *ntfsck_mount(const char *path __attribute__((unused)),
		ntfs_mount_flags flags __attribute__((unused)))
{
	ntfs_volume *vol;

	vol = ntfs_mount(path, flags);
	if (!vol)
		return NULL;

	fsck_lcn_bitmap_size = NTFS_BLOCK_SIZE;
	fsck_lcn_bitmap = ntfs_calloc(fsck_lcn_bitmap_size);
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

	return vol;
}

static void ntfsck_umount(ntfs_volume *vol)
{
	if (fsck_lcn_bitmap)
		free(fsck_lcn_bitmap);

	if (fsck_mft_bmp)
		free(fsck_mft_bmp);

	ntfs_umount(vol, FALSE);
}

static inline BOOL ntfsck_opened_ni_vol(s64 mft_num)
{
	BOOL is_opened = FALSE;

	switch (mft_num) {
	case FILE_MFT:
	case FILE_MFTMirr:
	case FILE_Volume:
	case FILE_Bitmap:
	case FILE_Secure:
	case FILE_root:
		is_opened = TRUE;
	}

	return is_opened;
}

static ntfs_inode *ntfsck_get_opened_ni_vol(ntfs_volume *vol, s64 mft_num)
{
	ntfs_inode *ni = NULL;

	switch (mft_num) {
	case FILE_MFT:
		ni = vol->mft_ni;
		break;
	case FILE_MFTMirr:
		ni = vol->mftmirr_ni;
		break;
	case FILE_Volume:
		ni = vol->vol_ni;
		break;
	case FILE_Bitmap:
		ni = vol->lcnbmp_ni;
		break;
	case FILE_Secure:
		ni = vol->secure_ni;
	}

	return ni;
}

static int ntfsck_check_system_files(ntfs_volume *vol)
{
	ntfs_inode *sys_ni, *root_ni;
	ntfs_attr_search_ctx *root_ctx, *sys_ctx;
	ntfs_index_context *ictx;
	FILE_NAME_ATTR *fn;
	s64 mft_num;
	int err;

	ntfs_log_info("Parse #%d: Check system files...\n", parse_count++);

	root_ni = ntfs_inode_open(vol, FILE_root);
	if (!root_ni) {
		ntfs_log_error("Couldn't open the root directory.\n");
		return 1;
	}

	root_ctx = ntfs_attr_get_search_ctx(root_ni, NULL);
	if (!root_ctx)
		goto close_inode;

	ictx = ntfs_index_ctx_get(root_ni, NTFS_INDEX_I30, 4);
	if (!ictx)
		goto put_attr_ctx;

	/*
	 * System MFT entries should be verified checked by ntfs_device_mount().
	 * Here just account number of clusters that is used by system MFT
	 * entries.
	 */
	for (mft_num = FILE_MFT; mft_num < FILE_first_user; mft_num++) {
		if (vol->major_ver < 3 && mft_num == FILE_Extend)
			continue;
		sys_ni = ntfsck_get_opened_ni_vol(vol, mft_num);
		if (!sys_ni) {
			if (mft_num == FILE_root)
				sys_ni = root_ni;
			else {
				sys_ni = ntfs_inode_open(vol, mft_num);
				if (!sys_ni) {
					ntfs_log_error("Failed to open %ld system file\n",
							mft_num);
					goto put_index_ctx;
				}
			}
		}

		ntfsck_update_lcn_bitmap(sys_ni);

		if (mft_num > FILE_Extend) {
			ntfs_inode_close(sys_ni);
			continue;
		}

		sys_ctx = ntfs_attr_get_search_ctx(sys_ni, NULL);
		if (!sys_ctx) {
			ntfs_inode_close(sys_ni);
			goto put_index_ctx;
		}

		err = ntfs_attr_lookup(AT_FILE_NAME, AT_UNNAMED, 0,
				CASE_SENSITIVE, 0, NULL, 0, sys_ctx);
		if (err) {
			ntfs_log_error("Failed to lookup file name attribute of %ld system file\n",
					mft_num);
			ntfs_attr_put_search_ctx(sys_ctx);
			ntfs_inode_close(sys_ni);
			goto put_index_ctx;
		}

		fn = (FILE_NAME_ATTR *)((u8 *)sys_ctx->attr +
				le16_to_cpu(sys_ctx->attr->value_offset));

		/*
		 * Index entries of system files must exist. Check whether
		 * the index entries for system files is in the $INDEX_ROOT
		 * of the $Root mft entry using ntfs_index_lookup().
		 */
		if (ntfs_index_lookup(fn, le32_to_cpu(sys_ctx->attr->value_length),
					ictx)) {
			ntfs_log_error("Failed to find index entry of %ld system file\n",
					mft_num);
			ntfs_attr_put_search_ctx(sys_ctx);
			ntfs_inode_close(sys_ni);
			goto put_index_ctx;
		}

		ntfs_index_ctx_reinit(ictx);
		ntfs_attr_put_search_ctx(sys_ctx);
		if (ntfsck_opened_ni_vol(mft_num) == TRUE)
			continue;
		ntfs_inode_close(sys_ni);
	}

put_index_ctx:
	ntfs_index_ctx_put(ictx);
put_attr_ctx:
	ntfs_attr_put_search_ctx(root_ctx);
close_inode:
	ntfs_inode_close(root_ni);

	return 0;
}

/**
 * main - Does just what C99 claim it does.
 *
 * For more details on arguments and results, check the man page.
 */
int main(int argc, char **argv)
{
	ntfs_volume *vol;
	const char *path;
	int c, errors = 0, ret;
	unsigned long mnt_flags;
	BOOL check_dirty_only = FALSE;

	ntfs_log_set_handler(ntfs_log_handler_outerr);

	ntfs_log_set_levels(NTFS_LOG_LEVEL_INFO);

	option.verbose = 0;
	opterr = 0;
	while ((c = getopt_long(argc, argv, "aCnpyhvV", opts, NULL)) != EOF) {
		switch (c) {
		case 'a':
		case 'p':
			if (option.flags & (NTFS_MNT_FS_NO_REPAIR |
						NTFS_MNT_FS_ASK_REPAIR |
						NTFS_MNT_FS_YES_REPAIR) ||
					check_dirty_only == TRUE) {
conflict_option:
				ntfs_log_error("\n%s: "
				"Only one of the optinos -a/-p, -C, -n, -r or -y may be specified.\n",
				NTFS_PROGS);

				exit(RETURN_USAGE_OR_SYNTAX_ERROR);
			}

			option.flags = NTFS_MNT_FS_AUTO_REPAIR;
			break;
		case 'C':	/* exclusive with others */
			if (option.flags & (NTFS_MNT_FS_AUTO_REPAIR |
							NTFS_MNT_FS_NO_REPAIR |
							NTFS_MNT_FS_ASK_REPAIR |
							NTFS_MNT_FS_YES_REPAIR)) {
				goto conflict_option;
			}

			check_dirty_only = TRUE;
			break;
		case 'n':
			if (option.flags & (NTFS_MNT_FS_AUTO_REPAIR |
						NTFS_MNT_FS_ASK_REPAIR |
						NTFS_MNT_FS_YES_REPAIR) ||
					check_dirty_only == TRUE) {
				goto conflict_option;
			}

			option.flags = NTFS_MNT_FS_NO_REPAIR | NTFS_MNT_RDONLY;
			break;
		case 'r':
			if (option.flags & (NTFS_MNT_FS_AUTO_REPAIR |
						NTFS_MNT_FS_NO_REPAIR |
						NTFS_MNT_FS_YES_REPAIR) ||
					check_dirty_only == TRUE) {
				goto conflict_option;
			}

			option.flags = NTFS_MNT_FS_ASK_REPAIR;
			break;
		case 'y':
			if (option.flags & (NTFS_MNT_FS_AUTO_REPAIR |
						NTFS_MNT_FS_NO_REPAIR |
						NTFS_MNT_FS_ASK_REPAIR) ||
					check_dirty_only == TRUE) {
				goto conflict_option;
			}

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
	option.flags |= NTFS_MNT_FSCK;

	/* If not set fsck repair option, set default fsck flags to ASK mode. */
	if (!(option.flags & (NTFS_MNT_FS_AUTO_REPAIR |
				NTFS_MNT_FS_NO_REPAIR |
				NTFS_MNT_FS_ASK_REPAIR |
				NTFS_MNT_FS_YES_REPAIR))) {
		option.flags |= NTFS_MNT_FS_ASK_REPAIR;
	}

	if (optind != argc - 1)
		usage(1);
	path = argv[optind];

	if (!ntfs_check_if_mounted(path, &mnt_flags)) {
		if ((mnt_flags & NTFS_MF_MOUNTED)) {
			if (!(mnt_flags & NTFS_MF_READONLY)) {
				ntfs_log_error("Refusing to operate on read-write mounted device %s.\n",
						path);
				exit(1);
			}

			if (option.flags != (NTFS_MNT_FS_NO_REPAIR | NTFS_MNT_RDONLY)) {
				ntfs_log_error("Refusing to change filesystem on read mounted device %s.\n",
						path);
				exit(1);
			}
		}
	} else
		ntfs_log_perror("Failed to determine whether %s is mounted",
				path);

	vol = ntfsck_mount(path, option.flags);
	if (!vol)
		goto err_out;

	/* Just return the volume dirty flags when '-C' option is specified. */
	if (check_dirty_only == TRUE) {
		if (vol->flags & VOLUME_IS_DIRTY) {
			if (option.verbose)
				ntfs_log_info("Check volume: Volume is dirty.\n");
			exit(RETURN_FS_ERRORS_LEFT_UNCORRECTED);
		} else {
			if (option.verbose)
				ntfs_log_warning("Check volume: Volume is clean.\n");
			exit(RETURN_FS_NO_ERRORS);
		}
	}

	ntfsck_check_system_files(vol);

	if (ntfsck_replay_log(vol))
		goto err_out;

	if (ntfsck_scan_index_entries(vol)) {
		ntfs_log_error("Stop processing fsck due to critical problems\n");
		goto err_out;
	}

	ntfsck_check_mft_records(vol);

	ntfsck_check_orphaned_clusters(vol);

err_out:
	errors = fsck_errors - fsck_fixes;
	if (errors) {
		ntfs_log_info("%d errors left (errors:%d, fixed:%d)\n",
				errors, fsck_errors, fsck_fixes);
		ret = RETURN_FS_ERRORS_LEFT_UNCORRECTED;
	} else {
		ntfs_log_info("Clean, No errors found or left (errors:%d, fixed:%d)\n",
				fsck_errors, fsck_fixes);
		if (fsck_fixes)
			ret = RETURN_FS_ERRORS_CORRECTED;
		else
			ret = RETURN_FS_NO_ERRORS;
	}

	if (!errors && vol)
		ntfsck_reset_dirty(vol);

	if (vol)
		ntfsck_umount(vol);

	return ret;
}
