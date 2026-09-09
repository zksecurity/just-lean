#!/bin/sh
# Build the Lean library as a static archive and link the C program against it (needs leanc = Lean's clang).
set -e
cd "$(dirname "$0")/.."
lake build MergeSort:static
SYSROOT=$(lean --print-prefix)
leanc -O2 -o ffi/main ffi/main.c -isystem /usr/include -isystem /usr/include/x86_64-linux-gnu \
  -I "$SYSROOT/include" .lake/build/lib/libmergesort_MergeSort.a \
  -L "$SYSROOT/lib/lean" -L "$SYSROOT/lib" -lInit -lStd -lleanrt -luv -lgmp
./ffi/main "${1:-1000000}"
