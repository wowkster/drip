#!/bin/bash

set -e

cargo run -- -o build/$1.s $1.drip
cargo run -- -o build/$1 $1.drip

chmod +x build/$1
build/$1