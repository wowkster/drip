#!/bin/bash

EXECUTABLE=$1

if [[ -z $EXECUTABLE ]]; then
    echo 'must specify executable path'
    exit
fi

# docker run --rm -i --platform linux/amd64 -v ./$EXECUTABLE:/a.out ubuntu:latest /a.out

# https://gist.github.com/securisec/b88cf9e89f957669b95043c9c380a26e
# ROSETTA_DEBUGSERVER_PORT=1234 /a.out & gdb -ex 'set architecture i386:x86-64' -ex 'target remote localhost:1234' -ex 'set disassembly-flavor intel' ./a.out
docker run -it --platform linux/amd64 --cap-add=SYS_PTRACE --security-opt seccomp=unconfined -v ./$EXECUTABLE:/a.out ubuntu:latest bash
