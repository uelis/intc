#!/bin/sh

llvm-link $1.bc salloc.s | opt -always-inline -O3 | llc -O3 | gcc -x assembler - -o $1

