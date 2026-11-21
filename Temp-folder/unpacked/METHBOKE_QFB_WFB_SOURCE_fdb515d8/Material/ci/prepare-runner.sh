#!/usr/bin/env bash
set -euo pipefail

# The external-only helper checks free space first and stops reclaiming SDKs as
# soon as its budget is met. It never removes workspace, compiler or cache data.
exec python3 "$(dirname "$0")/runner_disk.py" "$@"
