#!/bin/bash
set -e

curl https://elan.lean-lang.org/elan-init.sh -sSf | sh -s -- -y --default-toolchain leanprover/lean4:4.22.0-rc4
lake update
