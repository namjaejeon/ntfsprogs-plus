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

enum {
	NTFSCK_ASK_REPAIR = 0,
	NTFSCK_AUTO_REPAIR,
	NTFSCK_NO_REPAIR,
};

static struct {
	int verbose;
	int flags;
} option;


/**
 * usage
 */
__attribute__((noreturn))
static void usage(int ret)
{
	ntfs_log_info("ntfsck v%s (libntfs-3g)\n\n"
		      "Usage: ntfsck [options] device\n"
		      "-a, --auto		auto-repair. no questions.\n"
		      "-n, --just_check	just check and make no changes\n"
		      "-v, --verbose		verbose.\n"
		      "-V, --version		version.\n\n"
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
	{"auto",		no_argument,		NULL,	'a' },
	{"just_check",		no_argument,		NULL,	'n' },
	{"verbose",		no_argument,		NULL,	'v' },
	{"version",		no_argument,		NULL,	'V' },
	{NULL,			0,			NULL,	 0  }
};

/* Assuming NO_NTFS_DEVICE_DEFAULT_IO_OPS is not set */

static int errors = 0;

//static s64 mft_offset, mftmirr_offset;
static s64 current_mft_record;
static s64 prev_mft_record;

/**
 * This is just a preliminary volume.
 * Filled while checking the boot sector and used in the preliminary MFT check.
 */

#define check_failed(FORMAT, ARGS...) \
	do { \
		errors++; \
		ntfs_log_redirect(__FUNCTION__,__FILE__,__LINE__, \
				NTFS_LOG_LEVEL_ERROR,NULL,FORMAT,##ARGS); \
	} while (0);

/**
 * 0 success.
 * 1 fail.
 */
static int assert_u32_equal(u32 val, u32 ok, const char *name)
{
	if (val!=ok) {
		check_failed("Assertion failed for '%lld:%s'. should be 0x%x, "
			"was 0x%x.\n", (long long)current_mft_record, name,
			(int)ok, (int)val);
		//errors++;
		return 1;
	}
	return 0;
}

static int assert_u32_noteq(u32 val, u32 wrong, const char *name)
{
	if (val==wrong) {
		check_failed("Assertion failed for '%lld:%s'. should not be "
			"0x%x.\n", (long long)current_mft_record, name,
			(int)wrong);
		return 1;
	}
	return 0;
}

static int ntfsck_check_entries_index_root(MFT_RECORD *mft_rec, ATTR_REC *attr_rec)
{
	INDEX_ROOT *ir;
	u32 index_block_size;
	FILE_NAME_ATTR *fn;
	INDEX_ENTRY *ie;
	u8 *index_end;
	u16 value_offset = le16_to_cpu(attr_rec->value_offset);

	ir = (INDEX_ROOT *)((u8*)attr_rec + value_offset);

	index_block_size = le32_to_cpu(ir->index_block_size);
	if (index_block_size < NTFS_BLOCK_SIZE ||
			index_block_size & (index_block_size - 1)) {
		check_failed("Index block size %u is invalid.\n",
				(unsigned)index_block_size);
		goto out;
	}

	index_end = (u8 *)&ir->index + le32_to_cpu(ir->index.index_length);
	/* The first index entry. */
	ie = (INDEX_ENTRY *)((u8*)&ir->index +
			le32_to_cpu(ir->index.entries_offset));
	/*
	 * Loop until we exceed valid memory (corruption case) or until we
	 * reach the last entry or until filldir tells us it has had enough
	 * or signals an error (both covered by the rc test).
	 */
	for (;; ie = (INDEX_ENTRY *)((u8 *)ie + le16_to_cpu(ie->length))) {
		ntfs_log_verbose("In index root, offset %d.\n",
				(int)((u8 *)ie - (u8 *)ir));
		/* Bounds checks. */
		if ((u8 *)ie < (u8 *)mft_rec ||
				(u8 *)ie + sizeof(INDEX_ENTRY_HEADER) > index_end ||
				(u8 *)ie + le16_to_cpu(ie->length) > index_end) {
			goto out;
		}
		/* The last entry cannot contain a name. */
		if (ie->ie_flags & INDEX_ENTRY_END)
			return 0;

		if (!le16_to_cpu(ie->length))
			goto out;

		if (ie->key_length &&
				((le16_to_cpu(ie->key_length) + offsetof(INDEX_ENTRY, key)) >
				 le16_to_cpu(ie->length))) {
			check_failed("Overflow from index entry\n");
			goto out;
		} else if ((offsetof(INDEX_ENTRY, key.file_name.file_name) +
			    ie->key.file_name.file_name_length * sizeof(ntfschar)) >
			   le16_to_cpu(ie->length)) {
		/*	check_failed("mft_num : %lu, File name overflow from index entry\n",
					current_mft_record); */
			goto out;
		}

		fn = &ie->key.file_name;
		/* Skip root directory self reference entry. */
		ntfs_log_verbose("mft_num : %lu, Parent : 0x%lx, Indexed file : 0x%lx, File attribute : 0x%x, filename : %s\n",
				current_mft_record, MREF_LE(fn->parent_directory),
				MREF_LE(ie->indexed_file), ie->key.file_name.file_attributes,
				ntfs_attr_name_get(fn->file_name, fn->file_name_length));
	}

out:
	return 1;
}

ntfschar NTFS_INDEX_I30[5] = { const_cpu_to_le16('$'), const_cpu_to_le16('I'),
	const_cpu_to_le16('3'), const_cpu_to_le16('0'),
	const_cpu_to_le16('\0') };

static int ntfsck_check_entries_index_allocation(ntfs_volume *vol,
		ntfs_inode *inode)
{
	ntfs_attr *ia_na = NULL, *bmp_na = NULL;
	s64 br, ia_pos, bmp_pos, ia_start;
	ntfs_attr_search_ctx *ctx = NULL;
	u8 *index_end, *bmp = NULL;
	INDEX_ROOT *ir;
	INDEX_ENTRY *ie;
	INDEX_ALLOCATION *ia = NULL;
	int bmp_buf_size, bmp_buf_pos;
	u32 index_block_size;
	u8 index_block_size_bits, index_vcn_size_bits;
	FILE_NAME_ATTR *fn;
	u64 mft_no;
	u64 parent_mft_no;

	ia_na = ntfs_attr_open(inode, AT_INDEX_ALLOCATION, NTFS_INDEX_I30, 4);
	if (!ia_na) {
		check_failed("Failed to open index allocation attribute. Directory inode %lld is corrupt or bug\n",
			(long long)inode->mft_no);
		return -1;
	}

	ctx = ntfs_attr_get_search_ctx(inode, NULL);
	if (!ctx)
		goto err_out;

	/* Find the index root attribute in the mft record. */
	if (ntfs_attr_lookup(AT_INDEX_ROOT, NTFS_INDEX_I30, 4, CASE_SENSITIVE,
				0, NULL, 0, ctx)) {
		check_failed("Index root attribute missing in directory inode %lld\n",
				(unsigned long long)inode->mft_no);
		goto err_out;
	}
	/* Get to the index root value. */
	ir = (INDEX_ROOT *)((u8 *)ctx->attr +
			le16_to_cpu(ctx->attr->value_offset));

	index_block_size = le32_to_cpu(ir->index_block_size);
	index_block_size_bits = ffs(index_block_size) - 1;

	if (vol->cluster_size <= index_block_size)
		index_vcn_size_bits = vol->cluster_size_bits;
	else
		index_vcn_size_bits = NTFS_BLOCK_SIZE_BITS;

	/* Allocate a buffer for the current index block. */
	ia = ntfs_malloc(index_block_size);
	if (!ia)
		goto err_out;

	bmp_na = ntfs_attr_open(inode, AT_BITMAP, NTFS_INDEX_I30, 4);
	if (!bmp_na) {
		check_failed("Failed to open index bitmap attribute\n");
		goto err_out;
	}

	/* Get the offset into the index allocation attribute. */
	ia_pos = 0;

	bmp_pos = ia_pos >> index_block_size_bits;
	if (bmp_pos >> 3 >= bmp_na->data_size) {
		check_failed("Current index position exceeds index bitmap size.\n");
		goto err_out;
	}

	bmp_buf_size = min(bmp_na->data_size - (bmp_pos >> 3), 4096);
	bmp = ntfs_malloc(bmp_buf_size);
	if (!bmp)
		goto err_out;

	br = ntfs_attr_pread(bmp_na, bmp_pos >> 3, bmp_buf_size, bmp);
	if (br != bmp_buf_size) {
		check_failed("Failed to read from index bitmap attribute\n");
		goto err_out;
	}

	bmp_buf_pos = 0;
	/* If the index block is not in use find the next one that is. */
	while (!(bmp[bmp_buf_pos >> 3] & (1 << (bmp_buf_pos & 7)))) {
find_next_index_buffer:
		bmp_pos++;
		bmp_buf_pos++;
		/* If we have reached the end of the bitmap, we are done. */
		if (bmp_pos >> 3 >= bmp_na->data_size)
			goto EOD;
		ia_pos = bmp_pos << index_block_size_bits;
		if (bmp_buf_pos >> 3 < bmp_buf_size)
			continue;
		/* Read next chunk from the index bitmap. */
		bmp_buf_pos = 0;
		if ((bmp_pos >> 3) + bmp_buf_size > bmp_na->data_size)
			bmp_buf_size = bmp_na->data_size - (bmp_pos >> 3);
		br = ntfs_attr_pread(bmp_na, bmp_pos >> 3, bmp_buf_size, bmp);
		if (br != bmp_buf_size) {
			check_failed("Failed to read from index bitmap attribute\n");
			goto err_out;
		}
	}

	ntfs_log_verbose("Handling index block 0x%llx.\n", (long long)bmp_pos);

	/* Read the index block starting at bmp_pos. */
	br = ntfs_attr_mst_pread(ia_na, bmp_pos << index_block_size_bits, 1,
			index_block_size, ia);
	if (br != 1) {
		check_failed("Failed to read index block\n");
		goto err_out;
	}

	ia_start = ia_pos & ~(s64)(index_block_size - 1);
	if (ntfs_index_block_inconsistent((INDEX_BLOCK *)ia, index_block_size,
			ia_na->ni->mft_no, ia_start >> index_vcn_size_bits)) {
		check_failed("ntfs_index_block_inconsistent failed\n");
		goto err_out;
	}
	index_end = (u8 *)&ia->index + le32_to_cpu(ia->index.index_length);

	/* The first index entry. */
	ie = (INDEX_ENTRY *)((u8 *)&ia->index +
			le32_to_cpu(ia->index.entries_offset));
	/*
	 * Loop until we exceed valid memory (corruption case) or until we
	 * reach the last entry or until ntfs_filldir tells us it has had
	 * enough or signals an error (both covered by the rc test).
	 */
	for (;; ie = (INDEX_ENTRY *)((u8 *)ie + le16_to_cpu(ie->length))) {
		ntfs_log_verbose("In index allocation, offset 0x%llx.\n",
				(long long)ia_start + ((u8 *)ie - (u8 *)ia));
		/* Bounds checks. */
		if ((u8 *)ie < (u8 *)ia ||
		    (u8 *)ie + sizeof(INDEX_ENTRY_HEADER) > index_end ||
		    (u8 *)ie + le16_to_cpu(ie->length) > index_end) {
			check_failed("Index entry out of bounds in directory inode %lld.\n",
					(unsigned long long)inode->mft_no);
			goto err_out;
		}
		/* The last entry cannot contain a name. */
		if (ie->ie_flags & INDEX_ENTRY_END)
			break;

		if (!le16_to_cpu(ie->length)) {
			check_failed("ie->length is zero\n");
			goto err_out;
		}

		/* Skip index entry if continuing previous readdir. */
		if (ia_pos - ia_start > (u8 *)ie - (u8 *)ia)
			continue;

		/* The file name must not overflow from the entry */
		if (ntfs_index_entry_inconsistent(ie, COLLATION_FILE_NAME,
					inode->mft_no)) {
			check_failed("index entry is inconsistent\n");
			goto err_out;
		}

		fn = &ie->key.file_name;
		mft_no = MREF_LE(ie->indexed_file);
		parent_mft_no = MREF_LE(fn->parent_directory);
		ntfs_log_verbose("mft_num : %lu, Parent : 0x%lx, Indexed file : 0x%lx, File attribute : 0x%x, filename : %s\n",
			current_mft_record, parent_mft_no,
			mft_no, ie->key.file_name.file_attributes,
			ntfs_attr_name_get(fn->file_name, fn->file_name_length));
	}
	goto find_next_index_buffer;
EOD:
	free(ia);
	free(bmp);
	if (bmp_na)
		ntfs_attr_close(bmp_na);
	if (ia_na)
		ntfs_attr_close(ia_na);
	return 0;
err_out:
	ntfs_log_verbose("failed.\n");
	if (ctx)
		ntfs_attr_put_search_ctx(ctx);
	free(ia);
	free(bmp);
	if (bmp_na)
		ntfs_attr_close(bmp_na);
	if (ia_na)
		ntfs_attr_close(ia_na);
	return -1;
}

/**
 * @attr_rec: The attribute record to check
 * @mft_rec: The parent FILE record.
 * @buflen: The size of the FILE record.
 *
 * Return:
 *  NULL: Fatal error occured. Not sure where is the next record.
 *  otherwise: pointer to the next attribute record.
 *
 * The function only check fields that are inside this attr record.
 *
 * Assumes mft_rec is current_mft_record.
 */
static ATTR_REC *ntfsck_check_attr_record(ntfs_volume *vol, ntfs_inode *inode,
		ATTR_REC *attr_rec, MFT_RECORD *mft_rec, u16 buflen)
{
	u16 name_offset;
	u16 attrs_offset = le16_to_cpu(mft_rec->attrs_offset);
	u32 attr_type = le32_to_cpu(attr_rec->type);
	u32 length = le32_to_cpu(attr_rec->length);
	int err;

	// Check that this attribute does not overflow the mft_record
	if ((u8*)attr_rec + length >= ((u8*)mft_rec) + buflen) {
		check_failed("Attribute (0x%x) is larger than FILE record (%lld).\n",
				(int)attr_type, (long long)current_mft_record);
		return NULL;
	}

	ntfs_log_verbose("Attribute type : %x\n", attr_type);
	// Attr type must be a multiple of 0x10 and 0x10<=x<=0x100.
	if ((attr_type & ~0x0F0) && (attr_type != 0x100)) {
		check_failed("Unknown attribute type 0x%x.\n",
			(int)attr_type);
		goto check_attr_record_next_attr;
	}

	if (length < 24) {
		check_failed("Attribute %lld:0x%x Length too short (%u).\n",
			(long long)current_mft_record, (int)attr_type,
			(int)length);
		goto check_attr_record_next_attr;
	}

	// If this is the first attribute:
	// todo: instance number must be smaller than next_instance.
	if ((u8*)attr_rec == ((u8*)mft_rec) + attrs_offset) {
		if (!mft_rec->base_mft_record)
			assert_u32_equal(attr_type, 0x10,
				"First attribute type");
		// The following not always holds.
		// attr 0x10 becomes instance 1 and attr 0x40 becomes 0.
		//assert_u32_equal(attr_rec->instance, 0,
		//	"First attribute instance number");
	} else {
		assert_u32_noteq(attr_type, 0x10,
			"Not-first attribute type");
		// The following not always holds.
		//assert_u32_noteq(attr_rec->instance, 0,
		//	"Not-first attribute instance number");
	}
	//if (current_mft_record==938 || current_mft_record==1683 || current_mft_record==3152 || current_mft_record==22410)
	//printf("Attribute %ld:0x%x instance: %u isbase:%d.\n",
	//		current_mft_record, (int)attr_type, (int)le16_to_cpu(attr_rec->instance), (int)mft_rec->base_mft_record);
	// todo: instance is unique.

	// Check flags.
	if (attr_rec->flags & ~(const_cpu_to_le16(0xc0ff))) {
		check_failed("Attribute %lld:0x%x Unknown flags (0x%x).\n",
			(long long)current_mft_record, (int)attr_type,
			(int)le16_to_cpu(attr_rec->flags));
	}

	if (attr_rec->non_resident > 1) {
		check_failed("Attribute %lld:0x%x Unknown non-resident "
			"flag (0x%x).\n", (long long)current_mft_record,
			(int)attr_type, (int)attr_rec->non_resident);
		goto check_attr_record_next_attr;
	}

	name_offset = le16_to_cpu(attr_rec->name_offset);
	/*
	 * todo: name must be legal unicode.
	 * Not really, information below in urls is about filenames, but I
	 * believe it also applies to attribute names.  (Yura)
	 *  http://blogs.msdn.com/michkap/archive/2006/09/24/769540.aspx
	 *  http://blogs.msdn.com/michkap/archive/2006/09/10/748699.aspx
	 */

	if (attr_rec->non_resident) {
		// Make sure all the fields exist.
		if (length < 64) {
			check_failed("Non-resident attribute %lld:0x%x too short (%u).\n",
				(long long)current_mft_record, (int)attr_type,
				(int)length);
			goto check_attr_record_next_attr;
		}

		if (attr_rec->compression_unit && (length < 72)) {
			check_failed("Compressed attribute %lld:0x%x too short (%u).\n",
				(long long)current_mft_record, (int)attr_type,
				(int)length);
			goto check_attr_record_next_attr;
		}

		if (attr_rec->name_length && (attr_rec->name_offset >=
				attr_rec->mapping_pairs_offset)) {
			check_failed("name comes before mapping pairs.\n");
			goto check_attr_record_next_attr;
		}

		if (option.verbose && attr_rec->name_length) {
			ntfs_log_info("Attribute name : %s\n",
				ntfs_attr_name_get((ntfschar *)((u8 *)attr_rec +
								attr_rec->name_offset),
								attr_rec->name_length));
		}
		// todo: length==mapping_pairs_offset+length of compressed mapping pairs.
		// todo: mapping_pairs_offset is 8-byte aligned.
		if (attr_rec->mapping_pairs_offset & 0x7) {
			check_failed("mapping pairs offset should be 8-byte aligned\n");
			goto check_attr_record_next_attr;
		}

		// todo: lowest vcn <= highest_vcn
		if (attr_rec->lowest_vcn > attr_rec->highest_vcn) {
			check_failed("lowest vcn <= highest vcn\n");
			goto check_attr_record_next_attr;
		}
		// todo: if base record -> lowest vcn==0
		if (!mft_rec->base_mft_record && attr_rec->lowest_vcn) {
			check_failed("lowest vcn in base record should be zero\n");
			goto check_attr_record_next_attr;
		}

		// todo: lowest_vcn!=0 -> attribute list is used.
		// todo: lowest_vcn & highest_vcn are in the drive (0<=x<total clusters)

		// todo: mapping pairs agree with highest_vcn.
		// todo: compression unit == 0 or 4.
		if (attr_rec->compression_unit != 0 && attr_rec->compression_unit != 4) {
			check_failed("compression unit == 0 or 4\n");
			goto check_attr_record_next_attr;
		}
		// todo: reserved1 == 0.
		// todo: if not compressed nor sparse, initialized_size <= allocated_size and data_size <= allocated_size.
		if (attr_rec->flags != ATTR_IS_COMPRESSED && attr_rec->flags != ATTR_IS_SPARSE) {
			if (attr_rec->initialized_size > attr_rec->allocated_size) {
				check_failed("invalid size\n");
				goto check_attr_record_next_attr;
			} else if (attr_rec->data_size > attr_rec->allocated_size) {
				check_failed("invalid size\n");
				goto check_attr_record_next_attr;
			}
		} else {
		// todo: if compressed or sparse, allocated_size <= initialized_size and allocated_size <= data_size
			if (attr_rec->initialized_size < attr_rec->allocated_size) {
				check_failed("invalid size\n");
				goto check_attr_record_next_attr;
			} else if (attr_rec->data_size < attr_rec->allocated_size) {
				check_failed("invalid size\n");
				goto check_attr_record_next_attr;
			}
		}
		// todo: if mft_no!=0 and not compressed/sparse, data_size==initialized_size.
		// todo: if mft_no!=0 and compressed/sparse, allocated_size==initialized_size.
		// todo: what about compressed_size if compressed?
		// todo: attribute must not be 0x10, 0x30, 0x40, 0x60, 0x70, 0x90, 0xd0 (not sure about 0xb0, 0xe0, 0xf0)
		switch (attr_type) {
			case AT_STANDARD_INFORMATION:
			case AT_FILE_NAME:
			case AT_OBJECT_ID:
			case AT_VOLUME_NAME:
			case AT_VOLUME_INFORMATION:
			case AT_INDEX_ROOT:
			case AT_EA_INFORMATION:
				check_failed("Attribute must not be 0x10, 0x30, 0x40, 0x60, 0x70, 0x90, 0xd0 in non-resident\n");
				goto check_attr_record_next_attr;
		}

		if (attr_type == AT_INDEX_ALLOCATION)
			if (ntfsck_check_entries_index_allocation(vol, inode))
				goto check_attr_record_next_attr;

		// load runlist
		// vcn and lcn length check
		// if attribute list, check attrlist entry
	} else {
		u16 value_offset = le16_to_cpu(attr_rec->value_offset);
		u32 value_length = le32_to_cpu(attr_rec->value_length);
		// Resident
		if (attr_rec->name_length) {
			if (name_offset < 24)
				check_failed("Resident attribute with "
					"name intersecting header.\n");
			if (value_offset < name_offset +
					attr_rec->name_length)
				check_failed("Named resident attribute "
					"with value before name.\n");
		}

		if (option.verbose && attr_type == AT_FILE_NAME) {
			FILE_NAME_ATTR *fn = NULL;

			fn = (FILE_NAME_ATTR *)((u8*)attr_rec +
                                le16_to_cpu(attr_rec->value_offset));

			ntfs_log_info("MFT record name : %s\n",
					ntfs_attr_name_get(fn->file_name, fn->file_name_length));

		}

		// if resident, length==value_length+value_offset
		//assert_u32_equal(le32_to_cpu(attr_rec->value_length)+
		//	value_offset, length,
		//	"length==value_length+value_offset");
		// if resident, length==value_length+value_offset
		if (value_length + value_offset > length) {
			check_failed("value_length(%d) + value_offset(%d) > length(%d) for attribute 0x%x.\n",
					(int)value_length, (int)value_offset, (int)length, (int)attr_type);
			return NULL;
		}

		// Check resident_flags.
		if (attr_rec->resident_flags > 0x01) {
			check_failed("Unknown resident flags (0x%x) for attribute 0x%x.\n",
					(int)attr_rec->resident_flags, (int)attr_type);
		} else if (attr_rec->resident_flags && (attr_type != 0x30)) {
			check_failed("Resident flags mark attribute 0x%x as indexed.\n",
					(int)attr_type);
		}

		// reservedR is 0.
		assert_u32_equal(attr_rec->reservedR, 0, "Resident Reserved");

		// todo: attribute must not be 0xa0 (not sure about 0xb0, 0xe0, 0xf0)
		if (attr_type == AT_INDEX_ALLOCATION)
			check_failed("Index Allocation attribute can not be in resident entry\n");
		// todo: check content well-formness per attr_type.

		if (attr_type == AT_INDEX_ROOT) {
			err = ntfsck_check_entries_index_root(mft_rec, attr_rec);
			if (err)
				goto check_attr_record_next_attr;
		}

	}

check_attr_record_next_attr:
	return (ATTR_REC *)(((u8 *)attr_rec) + length);
}

/*
 * The sequence number for each of the system files is always equal to
 * their mft record number and it is never modified.
 */
static int ntfsck_check_seq_num_sys_files(ntfs_volume *vol, MFT_RECORD *mft_rec,
		s64 mft_num)
{
	int mft_rec_num = le32_to_cpu(mft_rec->mft_record_number);

	if (mft_num == FILE_MFT && mft_rec_num != FILE_MFT)
		goto err_out;
	else if (mft_num == FILE_MFTMirr && mft_rec_num != FILE_MFTMirr)
		goto err_out;
	else if (mft_num == FILE_LogFile && mft_rec_num != FILE_LogFile)
		goto err_out;
	else if (mft_num == FILE_Volume && mft_rec_num != FILE_Volume)
		goto err_out;
	else if (mft_num == FILE_AttrDef && mft_rec_num != FILE_AttrDef)
		goto err_out;
	else if (mft_num == FILE_root && mft_rec_num != FILE_root)
		goto err_out;
	else if (mft_num == FILE_Bitmap && mft_rec_num != FILE_Bitmap)
		goto err_out;
	else if (mft_num == FILE_Boot && mft_rec_num != FILE_Boot)
		goto err_out;
	else if (mft_num == FILE_BadClus && mft_rec_num != FILE_BadClus)
		goto err_out;
	else if (mft_num == FILE_Secure && mft_rec_num != FILE_Secure)
		goto err_out;
	else if (mft_num == FILE_UpCase && mft_rec_num != FILE_UpCase)
		goto err_out;
	else if (vol->major_ver >= 3 && mft_num == FILE_Extend &&
		 mft_rec_num != FILE_Extend)
		goto err_out;

	return 0;

err_out:
	return -1;
}

/**
 * All checks that can be satisfied only by data from the buffer.
 * No other [MFT records/metadata files] are required.
 *
 * The buffer is changed by removing the Update Sequence.
 *
 * Return:
 *	0	Everything's cool.
 *	else	Consider this record as damaged.
 */
static BOOL ntfsck_check_file_record(ntfs_volume *vol, u8 *buffer, u16 buflen,
		s64 mft_num)
{
	u16 usa_count, usa_ofs, attrs_offset, usa;
	u32 bytes_in_use, bytes_allocated, i;
	MFT_RECORD *mft_rec = (MFT_RECORD *)buffer;
	ATTR_REC *attr_rec;
	ntfs_inode *inode;
	int ret = 1;

	// check record magic
	if (le32_to_cpu(mft_rec->magic) != le32_to_cpu(magic_FILE)) {
		check_failed("FILE record magic(%x) should be %x\n",
				le32_to_cpu(mft_rec->magic), magic_FILE);
		return 1;
	}

	// todo: what to do with magic_BAAD?

	// check usa_count+offset to update seq <= attrs_offset <
	//	bytes_in_use <= bytes_allocated <= buflen.
	usa_ofs = le16_to_cpu(mft_rec->usa_ofs);
	usa_count = le16_to_cpu(mft_rec->usa_count);
	attrs_offset = le16_to_cpu(mft_rec->attrs_offset);
	bytes_in_use = le32_to_cpu(mft_rec->bytes_in_use);
	bytes_allocated = le32_to_cpu(mft_rec->bytes_allocated);
	if (usa_ofs + usa_count > attrs_offset) {
		check_failed("usa_ofs(%d) + usa_count(%d) beyond of attrs_offset(%d)\n",
				usa_ofs, usa_count, attrs_offset);
		return 1;
	}

	if (attrs_offset >= bytes_in_use) {
		check_failed("attrs_offset(%d) beyond(or same) of bytes_in_use(%d)\n",
				attrs_offset, bytes_in_use);
		return 1;
	}

	if (bytes_in_use > bytes_allocated) {
		check_failed("bytes_in_use(%d) beyond of bytes_allocated(%d)\n",
				bytes_in_use, bytes_allocated);
		return 1;
	}

	if (bytes_allocated > buflen) {
		check_failed("bytes_allocated(%d) beyond of mft record size(%d)\n",
				bytes_allocated, buflen);
		return 1;
	}

	// We should know all the flags.
	if (le16_to_cpu(mft_rec->flags) > 0xf) {
		check_failed("Unknown MFT record flags (0x%x).\n",
			(unsigned int)le16_to_cpu(mft_rec->flags));
		return 1;
	}

	if (ntfsck_check_seq_num_sys_files(vol, mft_rec, mft_num)) {
		check_failed("The sequence number(%lu) for each of the system file is not equal", mft_num);
		return 1;
	}

	if (mft_num >= 16 && mft_num <= 23) {
		if (prev_mft_record != mft_num - 1) {
			check_failed("records 16-23 must be filled in order. (prev : %ld, curr : %ld\n",
					prev_mft_record, mft_num);
			return 1;

		}

		if (mft_rec->flags & MFT_RECORD_IN_USE) {
			check_failed("MFT_RECORD_IN_USE in flags MFT record 16 ~ 23 must be off (0x%x).\n",
					(unsigned int)le16_to_cpu(mft_rec->flags));
			return 1;
		}
		prev_mft_record = mft_num;
	} else if (!(mft_rec->flags & MFT_RECORD_IN_USE)) {
		// flag in_use must be on.
		check_failed("MFT_RECORD_IN_USE in MFT record flags must be on (0x%x).\n",
			(unsigned int)le16_to_cpu(mft_rec->flags));
		return 1;
	} else
		prev_mft_record = mft_rec->mft_record_number;

	// Remove update seq & check it.
	usa = *(u16*)(buffer + usa_ofs); // The value that should be at the end of every sector.
	if (usa_count - 1 != buflen / NTFS_BLOCK_SIZE) {
		check_failed("USA length(%d) is invalid\n", usa_count - 1);
		return 1;
	}

	for (i = 1;i < usa_count; i++) {
		u16 *fixup = (u16*)(buffer + NTFS_BLOCK_SIZE * i - 2); // the value at the end of the sector.
		u16 saved_val = *(u16*)(buffer + usa_ofs + 2 * i); // the actual data value that was saved in the us array.

		if (*fixup != usa) {
			check_failed("invalid fixup\n");
			return 1;
		}
		*fixup = saved_val; // remove it.
	}

	inode = ntfs_inode_open(vol, mft_num);
	if (!inode) {
		ntfs_log_perror("ERROR: Couldn't open inode");
		return 1;
	}

	attr_rec = (ATTR_REC *)(buffer + attrs_offset);
	while ((u8*)attr_rec <= buffer + buflen - 4) {
		// Check attribute record. (Only what is in the buffer)
		if (attr_rec->type == AT_END) {
			// Done.
			ret = 0;
			goto close_inode;
		}

		if ((u8*)attr_rec > buffer + buflen - 8) {
			// not AT_END yet no room for the length field.
			check_failed("Attribute 0x%x is not AT_END, yet no "
					"room for the length field.\n",
					(int)le32_to_cpu(attr_rec->type));
			goto close_inode;
		}

		attr_rec = ntfsck_check_attr_record(vol, inode, attr_rec, mft_rec,
				buflen);
		if (!attr_rec)
			goto close_inode;
	}

close_inode:
	ntfs_inode_close(inode);
	// If we got here, there was an overflow.
	return ret;
	
	// todo: an attribute should be at the offset to first attribute, and the offset should be inside the buffer. It should have the value of "next attribute id".
	// todo: if base record, it should start with attribute 0x10.

	// Highlevel check of attributes.
	//  todo: Attributes are well-formed.
	//  todo: Room for next attribute in the end of the previous record.

	return FALSE;
}

static void ntfsck_replay_log(ntfs_volume *vol __attribute__((unused)))
{
	// At this time, only check that the log is fully replayed.
	// todo: if logfile is clean, return success.
}

static u8 *mft_bmp_index_buf;
static s64 mft_bmp_index_buf_size;

long long mfts_data_size;

u8 *fsck_lcn_bitmap;
unsigned int fsck_lcn_bitmap_size;

static void ntfsck_compare_bitmap(ntfs_volume *vol)
{
	s64 pos = 0, i, count;
	BOOL backup_boot_sec_bit = FALSE;
	u8 bm[NTFS_BUF_SIZE];

	while (1) {
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

			if (fsck_lcn_bitmap[pos] == bm[i])
				continue;

			for (cl = pos * 8; cl < (pos + 1) * 8; cl++) {
				char bit;

				/*
				 * Don't count cluster allocation bit for backup
				 * boot sector. Too much allocation bitmap for
				 * this bit is not need to be allocated.
				 */
				if (cl == vol->nr_clusters) {
					backup_boot_sec_bit = TRUE;
					continue;
				}

				bit = ntfs_bit_get(bm, i * 8 + cl % 8);
				if (ntfs_bit_get(fsck_lcn_bitmap, cl) != bit)
					ntfs_log_error("stale cluster bit : %ld\n", cl);
			}
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
		if (actx->attr->non_resident) {
			runlist *rl;
			int i = 0;

			rl = ntfs_mapping_pairs_decompress(ni->vol, actx->attr,
					NULL);
			if (!rl) {
				ntfs_log_error("Failed to decompress runlist.  Leaving inconsistent metadata.\n");
				continue;
			}

			while (rl[i].length && rl[i].lcn > (LCN)LCN_HOLE) {
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
						rl[i].lcn, rl->length, 1);
				i++;
			}

			free(rl);
		}
	}

	return 0;
}

static int ntfsck_verify_mft_record(ntfs_volume *vol, s64 mft_num)
{
	u8 *buffer;
	int is_used;
	int always_exist_sys_meta_num = vol->major_ver >= 3 ? 11 : 10;
	ntfs_inode *ni;

	current_mft_record = mft_num;

	is_used = utils_mftrec_in_use(vol, mft_num);
	if (is_used < 0) {
		ntfs_log_error("Error getting bit value for record %lld.\n",
			(long long)mft_num);
		return -1;
	} else if (!is_used) {
		if (mft_num <= always_exist_sys_meta_num) {
			ntfs_log_verbose("Record %lld unused. Fixing or fail about system files.\n",
					(long long)mft_num);
			errors++;
			return 0;
		}

		ntfs_log_verbose("Record %lld unused. Skipping.\n",
				(long long)mft_num);
		return 0;
	}

	buffer = ntfs_malloc(vol->mft_record_size);
	if (!buffer)
		goto verify_mft_record_error;

	ntfs_log_verbose("MFT record %lld\n", (long long)mft_num);
	if (ntfs_attr_pread(vol->mft_na, mft_num*vol->mft_record_size, vol->mft_record_size, buffer) < 0) {
		ntfs_log_perror("Couldn't read $MFT record %lld", (long long)mft_num);
		goto verify_mft_record_error;
	}

	is_used = ntfs_bit_get(mft_bmp_index_buf, mft_num);
	if (!is_used) {
		check_failed("Stale MFT Record %lld\n", (long long)mft_num);
		if (NVolFsRepair(vol)) {
			ntfs_log_verbose("Just clear the bit in the $MFT/$BITMAP corresponding stale MFT record\n");
			if (ntfs_bitmap_clear_bit(vol->mftbmp_na, mft_num)) {
				ntfs_log_error("ntfs_bitmap_clear_bit failed, errno : %d\n", errno);
				goto verify_mft_record_error;
			}
		}

		goto verify_mft_record_error;
	}

	ni = ntfs_inode_open(vol, mft_num);
	if (!ni) {
		ntfs_log_error("open failed : %ld\n", mft_num);
		goto verify_mft_record_error;
	}

	/*
	 * Update number of clusters that is used for each non-resident mft entries to
	 * bitmap.
	 */
	ntfsck_update_lcn_bitmap(ni);

	//ntfsck_check_file_record(vol, buffer, vol->mft_record_size, mft_num);
	// todo: if offset to first attribute >= 0x30, number of mft record should match.
	// todo: Match the "record is used" with the mft bitmap.
	// todo: if this is not base, check that the parent is a base, and is in use, and pointing to this record.

	// todo: if base record: for each extent record:
	//   todo: verify_file_record
	//   todo: hard link count should be the number of 0x30 attributes.
	//   todo: Order of attributes.
	//   todo: make sure compression_unit is the same.

	return 0;
verify_mft_record_error:

	if (buffer)
		free(buffer);
	errors++;
	return 0;
}

struct dir {
	struct ntfs_list_head list;
	ntfs_inode *ni;
};

struct ntfsls_dirent {
	ntfs_volume *vol;
};

NTFS_LIST_HEAD(ntfs_dirs_list);

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

static int ntfsck_add_dir_list(ntfs_volume *vol, INDEX_ENTRY *ie)
{
	char *filename = ntfs_ie_filename_get(ie);
	ntfs_inode *ni;
	struct dir *dir;
	MFT_REF mref;
	int ret = 0;

	if (!ie)
		return -1;

	mref = le64_to_cpu(ie->indexed_file);
	ntfs_log_verbose("%ld, %s\n", MREF(mref), filename);

	ni = ntfs_inode_open(vol, MREF(mref));
	if (ni) {
		if (MREF(mref) > mft_bmp_index_buf_size) {
			s64 off = mft_bmp_index_buf_size;

			mft_bmp_index_buf_size +=
				(MREF(mref) + 1 + (NTFS_BLOCK_SIZE - 1)) &
				 ~(NTFS_BLOCK_SIZE - 1);
			mft_bmp_index_buf = ntfs_realloc(mft_bmp_index_buf,
					mft_bmp_index_buf_size);
			memset(mft_bmp_index_buf + off, 0, mft_bmp_index_buf_size - off);
		}

		ntfs_bit_set(mft_bmp_index_buf, MREF(mref), 1);

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

		ictx = ntfs_index_ctx_get(dir->ni, NTFS_INDEX_I30, 4);
		if (!ictx) {
			ntfs_attr_put_search_ctx(ctx);
			goto err_out;
		}
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

		if (!(next->ie_flags & INDEX_ENTRY_END)) {
			ntfsck_add_dir_list(vol, next);
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
				ntfsck_add_dir_list(vol, next);
			}
		}

		while ((next = ntfs_index_next(next, ictx)) != NULL) {
			ntfsck_add_dir_list(vol, next);
		}

		ntfs_index_ctx_put(ictx);
		ntfs_inode_close(dir->ni);
		ntfs_list_del(&dir->list);
		free(dir);
	}

	return 0;
err_out:
	return -1;
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


static int ntfsck_scan_volume(ntfs_volume *vol)
{
	int result;

	result = ntfsck_scan_index_entries_btree(vol);
	result = ntfsck_scan_index_entries_bitmap(vol);

	return result;
}

static void ntfsck_check_mft_records(ntfs_volume *vol)
{
	s64 mft_num, nr_mft_records;
	int err;

	// For each mft record, verify that it contains a valid file record.
	nr_mft_records = vol->mft_na->initialized_size >>
			vol->mft_record_size_bits;
	ntfs_log_info("Checking %lld MFT records.\n", (long long)nr_mft_records);

	fsck_lcn_bitmap_size = NTFS_BLOCK_SIZE;
	fsck_lcn_bitmap = ntfs_calloc(NTFS_BLOCK_SIZE);
	if (!fsck_lcn_bitmap)
		return;

	/*
	 * System MFT entries should be verified checked by ntfs_device_mount().
	 * Here just account number of clusters that is used by system MFT
	 * entries.
	 */
	for (mft_num = 0; mft_num < FILE_first_user; mft_num++) {
		ntfs_inode *ni;

		ni = ntfs_inode_open(vol, mft_num);
		if (ni)
			ntfsck_update_lcn_bitmap(ni);
	}

	for (mft_num = FILE_first_user; mft_num < nr_mft_records; mft_num++) {
		err = ntfsck_verify_mft_record(vol, mft_num);
		if (err)
			break;
	}

	ntfsck_compare_bitmap(vol);

	return;
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

	option.flags = NTFSCK_ASK_REPAIR;
	option.verbose = 0;
	while ((c = getopt_long(argc, argv, "anhvV", opts, NULL)) != EOF) {
		switch (c) {
		case 'a':
			option.flags = NTFSCK_AUTO_REPAIR;
			break;
		case 'n':
			option.flags = NTFSCK_NO_REPAIR;
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

			if (option.flags != NTFSCK_NO_REPAIR) {
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

	/* Call ntfs_device_mount() to do the actual mount. */
	vol = ntfs_device_mount(dev,
			option.flags ==  NTFSCK_AUTO_REPAIR ?
			NTFS_MNT_FS_REPAIR : NTFS_MNT_FS_JUST_CHECK | NTFS_MNT_RDONLY);
	if (!vol) {
		ntfs_log_error("ntfs_device_mount failed\n");
		ntfs_device_free(dev);
		return 2;
	}

	ntfsck_replay_log(vol);

	if (vol->flags & VOLUME_IS_DIRTY)
		ntfs_log_warning("Volume is dirty.\n");

	ntfsck_scan_volume(vol);

	ntfsck_check_mft_records(vol);

	if (errors)
		ntfs_log_info("Errors found.\n");

	if (!errors) {
		ntfsck_reset_dirty(vol);
	}

	ntfs_umount(vol, FALSE);

	if (errors)
		return 1;
	return 0;
}

