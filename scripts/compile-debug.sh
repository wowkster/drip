#!/bin/bash

set -e

cargo run -- -o build/$1.s $1.drip
cargo run -- -o build/$1 $1.drip

chmod +x build/$1

ROSETTA_DEBUGSERVER_PORT=1234 build/$1 & gdb \
    -ex 'set architecture i386:x86-64' \
    -ex 'target remote localhost:1234' \
    -ex 'set disassembly-flavor intel' \
    -ex 'layout asm' \
    -ex 'list' \
    -ex 'b main' \
    build/$1
