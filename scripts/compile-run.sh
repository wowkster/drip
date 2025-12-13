#!/bin/bash

set -e

cargo run -- -o build/$1.s examples/$1.drip
cargo run -- -o build/$1 examples/$1.drip

chmod +x build/$1
build/$1