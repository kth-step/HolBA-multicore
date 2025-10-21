#!/bin/bash
DIR=$(dirname "${BASH_SOURCE[0]}")
source $DIR/../../../config.env.sh

set -e

case "$1" in
  RISCV)
	CROSS=$HOLBA_GCC_RISCV64_CROSS
	FLAGS="-march=rv64ia"
	;;
  AArch64)
	CROSS=$HOLBA_GCC_ARM8_CROSS
	;;
  *) echo "Unknown architecture in CROSS=$CROSS" >&2; exit 1 ;;
esac

AS=${CROSS}as
OBJDUMP=${CROSS}objdump

TMP_S=$(mktemp /tmp/XXXXXX.s)
TMP_BIN=${TMP_S}.bin
TMP_DA=${TMP_S}.da

cat - > $TMP_S
$AS $FLAGS $TMP_S -o $TMP_BIN
$OBJDUMP -d $TMP_BIN > $TMP_DA
printf $TMP_DA
