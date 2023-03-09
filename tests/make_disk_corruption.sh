#!/usr/bin/env bash

OFFSET=$1
LENGTH=$2
FILE=$3

IDX=0

END=$(expr $OFFSET + $LENGTH)
OFF=$OFFSET

echo "OFFSET:$OFFSET , END:$END , FILE:$FILE"

echo ""
# zero 1byte patten corruption test
echo "== zero 1byte patten corruption test =="
while [ "$OFF" -lt "$END" ]
do
	IDX=0
	PATTERN=0x00
	while [ $IDX -lt 2 ]
	do
		echo "OFFSET:$OFF , PATTERN:$PATTERN"
		sudo xfs_io -f -c "pwrite -S $PATTERN $OFF 1" $FILE

		sudo fsck.ntfs -a $FILE > /dev/null
		RET=$?
		if [ $RET -ne 0 ] && [ $RET -ne 1 ]; then
			sudo fsck.ntfs -n $FILE
			exit 1
		fi
		sudo fsck.ntfs -n $FILE > /dev/null
		RET=$?
		if [ $RET -ne 0 ] && [ $RET -ne 1 ]; then
			sudo fsck.ntfs -n $FILE
			exit 1
		fi

		IDX=$(expr $IDX + 1)
		if [ $IDX -eq 1 ]; then
			PATTERN=0xFF
		fi
	done
	OFF=$(expr $OFF + 1)
done

OFF=$OFFSET
# zero 2byte patten corruption test
echo ""
echo "== zero 2byte patten corruption test =="
while [ "$OFF" -lt "$END" ]
do
	IDX=0
	PATTERN=0x0000
	while [ $IDX -lt 2 ]
	do
		echo "OFFSET:$OFF , PATTERN:$PATTERN"
		sudo xfs_io -f -c "pwrite -S $PATTERN $OFF 2" $FILE

		sudo fsck.ntfs -a $FILE > /dev/null
		RET=$?
		if [ $RET -ne 0 ] && [ $RET -ne 1 ]; then
			sudo fsck.ntfs -n $FILE
			exit 1
		fi
		sudo fsck.ntfs -n $FILE > /dev/null
		RET=$?
		if [ $RET -ne 0 ] && [ $RET -ne 1 ]; then
			sudo fsck.ntfs -n $FILE
			exit 1
		fi

		IDX=$(expr $IDX + 1)
		if [ $IDX -eq 1 ]; then
			PATTERN=0xFFFF
		fi
	done
	OFF=$(expr $OFF + 2)
done

OFF=$OFFSET
# zero 4byte patten corruption test
echo ""
echo "== zero 4byte patten corruption test =="
while [ "$OFF" -lt "$END" ]
do
	IDX=0
	PATTERN=0x00000000
	while [ $IDX -lt 2 ]
	do
		echo "OFFSET:$OFF , PATTERN:$PATTERN"
		sudo xfs_io -f -c "pwrite -S $PATTERN $OFF 4" $FILE

		sudo fsck.ntfs -a $FILE > /dev/null
		RET=$?
		if [ $RET -ne 0 ] && [ $RET -ne 1 ]; then
			sudo fsck.ntfs -n $FILE
			exit 1
		fi
		sudo fsck.ntfs -n $FILE > /dev/null
		RET=$?
		if [ $RET -ne 0 ] && [ $RET -ne 1 ]; then
			sudo fsck.ntfs -n $FILE
			exit 1
		fi

		IDX=$(expr $IDX + 1)
		if [ $IDX -eq 1 ]; then
			PATTERN=0xFFFFFFFF
		fi
	done
	OFF=$(expr $OFF + 4)
done

OFF=$OFFSET
# zero 8byte patten corruption test
echo ""
echo "== zero 8byte patten corruption test =="
while [ "$OFF" -lt "$END" ]
do
	IDX=0
	PATTERN=0x0000000000000000
	while [ $IDX -lt 2 ]
	do
		echo "OFFSET:$OFF , PATTERN:$PATTERN"
		sudo xfs_io -f -c "pwrite -S $PATTERN $OFF 8" $FILE

		sudo fsck.ntfs -a $FILE > /dev/null
		RET=$?
		if [ $RET -ne 0 ] && [ $RET -ne 1 ]; then
			sudo fsck.ntfs -n $FILE
			exit 1
		fi
		sudo fsck.ntfs -n $FILE > /dev/null
		RET=$?
		if [ $RET -ne 0 ] && [ $RET -ne 1 ]; then
			sudo fsck.ntfs -n $FILE
			exit 1
		fi

		IDX=$(expr $IDX + 1)
		if [ $IDX -eq 1 ]; then
			PATTERN=0xFFFFFFFFFFFFFFFF
		fi
	done
	OFF=$(expr $OFF + 8)
done

echo "== finish making disk corruption =="
