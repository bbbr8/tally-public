#!/bin/bash
set -euo pipefail
cd "$(dirname "$0")"
if ! command -v python3 >/dev/null 2>&1; then
  echo 'Install Python 3.12 or newer from python.org.' >&2
  exit 1
fi
export TALLY_NO_EXPERIMENT_LOG=1
python3 -B tally.py --selftest
exec python3 -B tally.py
