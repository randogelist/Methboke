#!/usr/bin/env bash
set -euo pipefail

# No host credential directory or Docker socket is mounted into this container.
mkdir -p /workspace /opt/material-registry
# --checksum plus --no-times preserves mtime when contents are unchanged.
# Existing Lake traces, dependency sources and object files remain in .lake.
# Deleted/changed checked-in source files are synchronized before Lake runs.
rsync -a --no-times --omit-dir-times --checksum --delete \
  --exclude='/.git/' \
  --exclude='/Material/.lake/' \
  --exclude='/Material/registry/current.json' \
  --exclude='/Material/registry/audits/' \
  --exclude='/Material/registry/history/' \
  /incoming/ /workspace/
cd /workspace
python3 Material/ci/build.py --report Material/registry/current.json

# The installed objects/traces remain in .lake. Completed download archives
# are reproducible transfer inputs and need not inflate every registry image.
python3 - <<'PY'
import json
from pathlib import Path
archives = list(Path('/root/.cache/mathlib').glob('*.ltar'))
removed_count = 0
removed_bytes = 0
for path in archives:
    if path.is_file() and not path.is_symlink():
        removed_bytes += path.stat().st_size
        path.unlink()
        removed_count += 1
target = Path('Material/registry/image-optimization.json')
target.parent.mkdir(parents=True, exist_ok=True)
target.write_text(json.dumps({
    'removed_completed_mathlib_download_archives': removed_count,
    'removed_bytes': removed_bytes,
    'retained': ['.lake/packages', '.lake/build', 'toolchain', 'source', 'audit logs'],
}, indent=2) + '\n')
PY
