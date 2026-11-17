#!/usr/bin/env bash
set -euo pipefail

# Only disposable GitHub-hosted runners; never developer/self-hosted machines.
if [[ "${GITHUB_ACTIONS:-}" != "true" || "${RUNNER_ENVIRONMENT:-}" != "github-hosted" ]]; then
  echo 'SDK reclamation skipped outside a disposable GitHub-hosted runner.'
  exit 0
fi

df -h /
# These preinstalled SDKs are unrelated to the pinned Lean/Python/Docker build.
# Fixed allowlist only: no workspace, toolchain, registry or Docker cache paths.
for sdk in /usr/local/lib/android /usr/share/dotnet /opt/ghc /usr/local/.ghcup; do
  if [[ -d "$sdk" && ! -L "$sdk" ]]; then
    sudo du -sh -- "$sdk"
    sudo rm -rf -- "$sdk"
  fi
done
df -h /
