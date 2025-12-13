#!/bin/bash

set -e

cargo run -- -e lir examples/$1.drip
