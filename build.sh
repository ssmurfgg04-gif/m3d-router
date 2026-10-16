#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
cc -O2 -Wall -Wno-misleading-indentation -o m3droute m3droute.c -lm
echo "built $(pwd)/m3droute"
