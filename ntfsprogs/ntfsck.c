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

#define DEFAULT_SECTOR_SIZE 512

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
//static ntfs_volume vol;

static runlist_element *mft_rl, *mft_bitmap_rl;

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

/*
 *		Try an alternate boot sector and fix the real one
 *
 *	Only after successful checks is the boot sector rewritten.
 *
 *	The alternate boot sector is not rewritten, either because it
 *	was found correct, or because we truncated the file system
 *	and the last actual sector might be part of some file.
 *
 *	Returns 0 if successful
 */

static int ntfsck_fix_boot_sector(ntfs_volume *vol, char *full_bs,
		s64 read_sector, s64 fix_sectors, s32 sector_size)
{
	s64 br;
	int res;
	s64 got_sectors;
	le16 sector_size_le;
	NTFS_BOOT_SECTOR *bs;

	res = -1;
	br = ntfs_pread(vol->dev, read_sector*sector_size, sector_size, full_bs);
	if (br != sector_size) {
		if (br != -1)
			errno = EINVAL;
		if (!br)
			ntfs_log_error("Failed to read alternate bootsector (size=0)\n");
		else
			ntfs_log_perror("Error reading alternate bootsector");
	} else {
		bs = (NTFS_BOOT_SECTOR *)full_bs;
		got_sectors = sle64_to_cpu(bs->number_of_sectors);
		bs->number_of_sectors = cpu_to_sle64(fix_sectors);
		/* alignment problem on Sparc, even doing memcpy() */
		sector_size_le = cpu_to_le16(sector_size);
		if (!memcmp(&sector_size_le, &bs->bpb.bytes_per_sector, 2) &&
		    ntfs_boot_sector_is_ntfs(bs) &&
		    !ntfs_boot_sector_parse(vol, bs)) {
			s64 bw;

			ntfs_log_info("The alternate bootsector is usable\n");
			if (fix_sectors != got_sectors)
				ntfs_log_info("Set sector count to %lld instead of %lld\n",
						(long long)fix_sectors,
						(long long)got_sectors);
			/* fix the normal boot sector */
			ntfs_log_info("Rewriting the bootsector\n");
			bw = ntfs_pwrite(vol->dev, 0, sector_size, full_bs);
			if (bw == sector_size)
				res = 0;
			else {
				if (bw != -1)
					errno = EINVAL;
				if (!bw)
					ntfs_log_error("Failed to rewrite the bootsector (size=0)\n");
				else
					ntfs_log_perror("Error rewriting the bootsector");
			}
		}
		if (!res)
			ntfs_log_verbose("The boot sector has been rewritten\n");
	}
	return res;
}

/**
 * Return: 0 ok, 1 error.
 */
static BOOL verify_boot_sector(ntfs_volume *rawvol)
{;
	NTFS_BOOT_SECTOR *ntfs_boot;
	s32 sector_size;
	struct ntfs_device *dev = rawvol->dev;

	current_mft_record = 9;

	sector_size = ntfs_device_sector_size_get(dev);
	if (sector_size <= 0)
		sector_size = DEFAULT_SECTOR_SIZE;

	ntfs_boot = ntfs_malloc(sizeof(NTFS_BOOT_SECTOR));
	if (!ntfs_boot)
		return 1;

	if (ntfs_pread(dev, 0, sector_size, ntfs_boot) != sector_size) {
		check_failed("Failed to read boot sector.\n");
		return 1;
	}

	if ((ntfs_boot->jump[0] != 0xeb) ||
	    ((ntfs_boot->jump[1] != 0x52) && (ntfs_boot->jump[1] != 0x5b)) ||
	    (ntfs_boot->jump[2] != 0x90)) {
		check_failed("Boot sector: Bad jump.\n");
		return 1;
	}

	if (!ntfs_boot_sector_is_ntfs(ntfs_boot) ||
	    (ntfs_boot_sector_parse(rawvol, ntfs_boot) < 0)) {
		int res = 1;

		if (option.flags == NTFSCK_AUTO_REPAIR) {
			s64 actual_sectors, shown_sectors;

			actual_sectors = ntfs_device_size_get(dev, sector_size) - 1;
			shown_sectors = sle64_to_cpu(ntfs_boot->number_of_sectors);
			/* first try the actual last sector */
			if ((actual_sectors > 0) &&
			    !ntfsck_fix_boot_sector(rawvol, (char *)ntfs_boot, actual_sectors,
						    actual_sectors, sector_size))
				res = 0;

			/* then try the shown last sector, if less than actual */
			if (res && (shown_sectors > 0) &&
			    (shown_sectors < actual_sectors) &&
			    !ntfsck_fix_boot_sector(rawvol, (char *)ntfs_boot, shown_sectors,
						    shown_sectors, sector_size))
				res = 0;

			/* then try reducing the number of sectors to actual value */
			if (res && (shown_sectors > actual_sectors) &&
			    !ntfsck_fix_boot_sector(rawvol, (char *)ntfs_boot, 0, actual_sectors,
						    sector_size))
				res = 0;
			if (res) {
				check_failed("Boot sector: failed to fix boot sector\n");
				return res;
			}
		} else if (res) {
			check_failed("Boot sector: invalid boot sector\n");
			return 1;
		}
	}

	// todo: if partition, query bios and match heads/tracks?
	return 0;
}

/**
 * Load the runlist of the <attr_type> attribute.
 *
 * Return NULL if an error.
 * The caller is responsible on freeing the allocated memory if the result is not NULL.
 *
 * Set size_of_file_record to some reasonable size when in doubt (the Windows default is 1024.)
 *
 * attr_type must be little endian.
 *
 * This function has code duplication with check_file_record() and
 * check_attr_record() but its goal is to be less strict. Thus the
 * duplicated checks are the minimal required for not crashing.
 *
 * Assumes dev is open.
 */
static runlist *load_runlist(ntfs_volume *rawvol, s64 offset_to_file_record, ATTR_TYPES attr_type, u32 size_of_file_record)
{
	u8 *buf;
	u16 attrs_offset;
	u32 length;
	ATTR_RECORD *attr_rec;
	
	if (size_of_file_record<22) // offset to attrs_offset
		return NULL;

	buf = (u8*)ntfs_malloc(size_of_file_record);
	if (!buf)
		return NULL;

	if (ntfs_pread(rawvol->dev, offset_to_file_record, size_of_file_record, buf) !=
			size_of_file_record) {
		check_failed("Failed to read file record at offset %lld (0x%llx).\n",
					(long long)offset_to_file_record,
					(long long)offset_to_file_record);
		return NULL;
	}

	attrs_offset = le16_to_cpu(((MFT_RECORD*)buf)->attrs_offset);
	// first attribute must be after the header.
	if (attrs_offset<42) {
		check_failed("First attribute must be after the header (%u).\n", (int)attrs_offset);
	}
	attr_rec = (ATTR_RECORD *)(buf + attrs_offset);
	//printf("uv1.\n");

	while ((u8*)attr_rec<=buf+size_of_file_record-4) {

		//printf("Attr type: 0x%x.\n", attr_rec->type);
		// Check attribute record. (Only what is in the buffer)
		if (attr_rec->type==AT_END) {
			check_failed("Attribute 0x%x not found in file record at offset %lld (0x%llx).\n", (int)le32_to_cpu(attr_rec->type),
					(long long)offset_to_file_record,
					(long long)offset_to_file_record);
			return NULL;
		}
		if ((u8*)attr_rec>buf+size_of_file_record-8) {
			// not AT_END yet no room for the length field.
			check_failed("Attribute 0x%x is not AT_END, yet no "
					"room for the length field.\n",
					(int)le32_to_cpu(attr_rec->type));
			return NULL;
		}

		length = le32_to_cpu(attr_rec->length);

		// Check that this attribute does not overflow the mft_record
		if ((u8*)attr_rec+length >= buf+size_of_file_record) {
			check_failed("Attribute (0x%x) is larger than FILE record at offset %lld (0x%llx).\n",
					(int)le32_to_cpu(attr_rec->type),
					(long long)offset_to_file_record,
					(long long)offset_to_file_record);
			return NULL;
		}
		// todo: what ATTRIBUTE_LIST (0x20)?

		if (attr_rec->type==attr_type) {
			// Eurika!

			// ntfs_mapping_pairs_decompress only use two values from vol. Just fake it.
			// todo: it will also use vol->major_ver if defined(DEBUG). But only for printing purposes.

			// Assume ntfs_boot_sector_parse() was called.
			return ntfs_mapping_pairs_decompress(rawvol, attr_rec, NULL);
		}

		attr_rec = (ATTR_RECORD*)((u8*)attr_rec+length);
	}
	// If we got here, there was an overflow.
	check_failed("file record corrupted at offset %lld (0x%llx).\n",
			(long long)offset_to_file_record,
			(long long)offset_to_file_record);
	return NULL;
}

/**
 * Return: >=0 last VCN
 *	   LCN_EINVAL error.
 */
static VCN get_last_vcn(runlist *rl)
{
	VCN res;

	if (!rl)
		return LCN_EINVAL;

	res = LCN_EINVAL;
	while (rl->length) {
		ntfs_log_verbose("vcn: %lld, length: %lld.\n",
				(long long)rl->vcn, (long long)rl->length);
		if (rl->vcn<0)
			res = rl->vcn;
		else
			res = rl->vcn + rl->length;
		rl++;
	}

	return res;
}

static u32 mft_bitmap_records;
static u8 *mft_bitmap_buf;

/**
 * Assumes mft_bitmap_rl is initialized.
 * return: 0 ok.
 *	   RETURN_OPERATIONAL_ERROR on error.
 */
static int mft_bitmap_load(ntfs_volume *rawvol)
{
	VCN vcn;
	u32 mft_bitmap_length;

	vcn = get_last_vcn(mft_bitmap_rl);
	if (vcn<=LCN_EINVAL) {
		mft_bitmap_buf = NULL;
		/* This case should not happen, not even with on-disk errors */
		goto error;
	}

	mft_bitmap_length = vcn * rawvol->cluster_size;
	mft_bitmap_records = 8 * mft_bitmap_length * rawvol->cluster_size /
		rawvol->mft_record_size;

	mft_bitmap_buf = (u8*)ntfs_malloc(mft_bitmap_length);
	if (!mft_bitmap_buf)
		goto error;
	if (ntfs_rl_pread(rawvol, mft_bitmap_rl, 0, mft_bitmap_length,
			mft_bitmap_buf) != mft_bitmap_length)
		goto error;

	return 0;
error:
	mft_bitmap_records = 0;
	ntfs_log_error("Could not load $MFT/Bitmap.\n");
	return RETURN_OPERATIONAL_ERROR;
}

/**
 * -1 Error.
 *  0 Unused record
 *  1 Used record
 *
 * Assumes mft_bitmap_rl was initialized.
 */
static int mft_bitmap_get_bit(s64 mft_no)
{
	if (mft_no>=mft_bitmap_records)
		return -1;
	return ntfs_bit_get(mft_bitmap_buf, mft_no);
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
static ATTR_REC *check_attr_record(ATTR_REC *attr_rec, MFT_RECORD *mft_rec,
			u16 buflen)
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
					ntfs_attr_name_get((ntfschar *)((u8 *)attr_rec + attr_rec->name_offset),
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
static BOOL check_file_record(u8 *buffer, u16 buflen, s64 mft_num)
{
	u16 usa_count, usa_ofs, attrs_offset, usa;
	u32 bytes_in_use, bytes_allocated, i;
	MFT_RECORD *mft_rec = (MFT_RECORD *)buffer;
	ATTR_REC *attr_rec;

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

	attr_rec = (ATTR_REC *)(buffer + attrs_offset);
	while ((u8*)attr_rec <= buffer + buflen - 4) {
		// Check attribute record. (Only what is in the buffer)
		if (attr_rec->type == AT_END) {
			// Done.
			return 0;
		}

		if ((u8*)attr_rec > buffer + buflen - 8) {
			// not AT_END yet no room for the length field.
			check_failed("Attribute 0x%x is not AT_END, yet no "
					"room for the length field.\n",
					(int)le32_to_cpu(attr_rec->type));
			return 1;
		}

		attr_rec = check_attr_record(attr_rec, mft_rec, buflen);
		if (!attr_rec)
			return 1;
	}
	// If we got here, there was an overflow.
	return 1;
	
	// todo: an attribute should be at the offset to first attribute, and the offset should be inside the buffer. It should have the value of "next attribute id".
	// todo: if base record, it should start with attribute 0x10.

	// Highlevel check of attributes.
	//  todo: Attributes are well-formed.
	//  todo: Room for next attribute in the end of the previous record.

	return FALSE;
}

static void replay_log(ntfs_volume *vol __attribute__((unused)))
{
	// At this time, only check that the log is fully replayed.
	// todo: if logfile is clean, return success.
}

static int verify_mft_record(ntfs_volume *vol, s64 mft_num)
{
	u8 *buffer;
	int is_used;

	current_mft_record = mft_num;

	is_used = mft_bitmap_get_bit(mft_num);
	if (is_used < 0) {
		ntfs_log_error("Error getting bit value for record %lld.\n",
			(long long)mft_num);
		return -1;
	} else if (!is_used) {
		if (mft_num < 16 && mft_num > 23) {
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

	check_file_record(buffer, vol->mft_record_size, mft_num);
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

/**
 * This function serves as bootstraping for the more comprehensive checks.
 * It will load the MFT runlist and MFT/Bitmap runlist.
 * It should not depend on other checks or we may have a circular dependancy.
 * Also, this loadng must be forgiving, unlike the comprehensive checks.
 */
static int verify_mft_preliminary(ntfs_volume *rawvol)
{
	current_mft_record = 0;
	s64 mft_offset, mftmirr_offset;
	int res;

	ntfs_log_trace("Entering verify_mft_preliminary().\n");
	// todo: get size_of_file_record from boot sector
	// Load the first segment of the $MFT/DATA runlist.
	mft_offset = rawvol->mft_lcn * rawvol->cluster_size;
	mftmirr_offset = rawvol->mftmirr_lcn * rawvol->cluster_size;
	mft_rl = load_runlist(rawvol, mft_offset, AT_DATA, 1024);
	if (!mft_rl) {
		check_failed("Loading $MFT runlist failed. Trying $MFTMirr.\n");
		mft_rl = load_runlist(rawvol, mftmirr_offset, AT_DATA, 1024);
	}
	if (!mft_rl) {
		check_failed("Loading $MFTMirr runlist failed too. Aborting.\n");
		return RETURN_FS_ERRORS_LEFT_UNCORRECTED | RETURN_OPERATIONAL_ERROR;
	}
	// TODO: else { recover $MFT } // Use $MFTMirr to recover $MFT.
	// todo: support loading the next runlist extents when ATTRIBUTE_LIST is used on $MFT.
	// If attribute list: Gradually load mft runlist. (parse runlist from first file record, check all referenced file records, continue with the next file record). If no attribute list, just load it.

	// Load the runlist of $MFT/Bitmap.
	// todo: what about ATTRIBUTE_LIST? Can we reuse code?
	mft_bitmap_rl = load_runlist(rawvol, mft_offset, AT_BITMAP, 1024);
	if (!mft_bitmap_rl) {
		check_failed("Loading $MFT/Bitmap runlist failed. Trying $MFTMirr.\n");
		mft_bitmap_rl = load_runlist(rawvol, mftmirr_offset, AT_BITMAP, 1024);
	}
	if (!mft_bitmap_rl) {
		check_failed("Loading $MFTMirr/Bitmap runlist failed too. Aborting.\n");
		return RETURN_FS_ERRORS_LEFT_UNCORRECTED;
		// todo: rebuild the bitmap by using the "in_use" file record flag or by filling it with 1's.
	}

	/* Load $MFT/Bitmap */
	if ((res = mft_bitmap_load(rawvol)))
		return res;
	return -1; /* FIXME: Just added to fix compiler warning without
			thinking about what should be here.  (Yura) */
}

static void check_volume(ntfs_volume *vol)
{
	s64 mft_num, nr_mft_records;
	int err;

	// For each mft record, verify that it contains a valid file record.
	nr_mft_records = vol->mft_na->initialized_size >>
			vol->mft_record_size_bits;
	ntfs_log_info("Checking %lld MFT records.\n", (long long)nr_mft_records);

	for (mft_num = 0; mft_num < nr_mft_records; mft_num++) {
		err = verify_mft_record(vol, mft_num);
		if (err)
			break;
	}

	// todo: Check metadata files.

	// todo: Second pass on mft records. Now check the contents as well.
	// todo: When going through runlists, build a bitmap.

	// todo: cluster accounting.
	return;
}

static int reset_dirty(ntfs_volume *vol)
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
	ntfs_volume rawvol;
	ntfs_volume *vol;
	const char *name;
	int ret, c;
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

	if (dev->d_ops->open(dev, O_RDWR)) {
		ntfs_log_perror("Error opening partition device");
		ntfs_device_free(dev);
		return RETURN_OPERATIONAL_ERROR;
	}

	rawvol.dev = dev;
	ret = verify_boot_sector(&rawvol);
	if (ret) {
		dev->d_ops->close(dev);
		return ret;
	}
	ntfs_log_verbose("Boot sector verification complete. Proceeding to $MFT");

	verify_mft_preliminary(&rawvol);

	/* ntfs_device_mount() expects the device to be closed. */
	if (dev->d_ops->close(dev))
		ntfs_log_perror("Failed to close the device.");

	// at this point we know that the volume is valid enough for mounting.

	/* Call ntfs_device_mount() to do the actual mount. */
	vol = ntfs_device_mount(dev,
			option.flags == NTFSCK_NO_REPAIR ? NTFS_MNT_RDONLY : 0);
	if (!vol) {
		ntfs_device_free(dev);
		return 2;
	}

	replay_log(vol);

	if (vol->flags & VOLUME_IS_DIRTY)
		ntfs_log_warning("Volume is dirty.\n");

	check_volume(vol);

	if (errors)
		ntfs_log_info("Errors found.\n");

	if (!errors) {
		reset_dirty(vol);
	}

	ntfs_umount(vol, FALSE);

	if (errors)
		return 1;
	return 0;
}

