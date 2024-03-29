#!/usr/bin/env bash

TESTCASE_DIR=$1
NEED_LOOPDEV=$2
IMAGE_FILE=ntfs.img
FSCK_PROG=ntfsck
FSCK_PROG_2=ntfsck
FSCK_OPTS_AUTO="-a"
FSCK_OPTS_CHECK="-n"
PASS_COUNT=0

cleanup() {
	echo ""
	echo "Passed ${PASS_COUNT} of ${TEST_COUNT}"
	if [ ${PASS_COUNT} -ne ${TEST_COUNT} ]; then
		exit 1
	else
		exit 0
	fi
}

if [ $# -eq 0 ]; then
	TESTCASE_DIRS=$(find . -mindepth 1 -maxdepth 1 -type d)
	TEST_COUNT=$(find . -mindepth 1 -maxdepth 1 -type d | wc -l)
else
	TESTCASE_DIRS=$@
	TEST_COUNT=$#
fi

for TESTCASE_DIR in $TESTCASE_DIRS; do
	if [ ! -e "${TESTCASE_DIR}/${IMAGE_FILE}.tar.gz" ]; then
		TEST_COUNT=$((TEST_COUNT - 1))
		continue
	fi

	echo ""
	echo "Running ${TESTCASE_DIR}"

	# Set up image file as loop device
	tar -C . -xf "${TESTCASE_DIR}/${IMAGE_FILE}.tar.gz"
	if [ $NEED_LOOPDEV ]; then
		DEV_FILE=$(losetup -f "${IMAGE_FILE}" --show)
	else
		DEV_FILE=$IMAGE_FILE
	fi

	# Run fsck for repair
	$FSCK_PROG $FSCK_OPTS_AUTO "$DEV_FILE"
	RET=$?
	if [ ${RET} -ne 1 ] && [ ${RET} -ne 0 ]; then
		echo ""
		echo "Failed to repair ${TESTCASE_DIR}"
		if [ $NEED_LOOPDEV ]; then
			losetup -d "${DEV_FILE}"
		fi
		cleanup
	fi

	echo ""
	# Run fsck again
	$FSCK_PROG_2 $FSCK_OPTS_CHECK "$DEV_FILE"
	RET=$?
	if [ ${RET} -ne 0 ]; then
		echo ""
		echo "Failed, corrupted ${TESTCASE_DIR}"
		if [ $NEED_LOOPDEV ]; then
			losetup -d "${DEV_FILE}"
		fi
		cleanup
	fi

	echo ""
	echo "Passed ${TESTCASE_DIR}"
	echo "-----------------------------------"
	PASS_COUNT=$((PASS_COUNT + 1))

	if [ $NEED_LOOPDEV ]; then
		losetup -d "${DEV_FILE}"
	fi
done
cleanup
