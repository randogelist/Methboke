#!/usr/bin/env bash
# External CI only. The caller supplies exact compatible restore identities.
set -euo pipefail
if [ "${CI:-}" != true ]; then
  echo 'External CI execution is required.' >&2
  exit 1
fi

extra=()
if [ "${EXACT_BENCHMARK:-false}" = true ]; then extra+=(--benchmark); fi
if [ "${REGISTRY_RESTORED:-false}" = true ]; then
  if [[ ! "${MATERIAL_PARENT_IMAGE_DIGEST:-}" =~ ^ghcr\.io/[^[:space:]]+@sha256:[0-9a-f]{64}$ ]]; then
    echo 'An immutable passed-image digest is required.' >&2
    exit 1
  fi
  if [ "${EXACT_BENCHMARK:-false}" = true ]; then
    echo 'Exact-cache benchmarking uses the native Actions-cache path.' >&2
    exit 1
  fi
  # `elan which` only resolves the already installed toolchain; it does not run Lean.
  lean_binary="$(cd Material && elan which lean)"
  lean_binary="$(readlink -f "$lean_binary")"
  toolchain_root="$(dirname "$(dirname "$lean_binary")")"
  test -x "$toolchain_root/bin/lean"
  test -x "$toolchain_root/bin/lake"
  # Bind the same absolute workspace path to preserve generated path identities.
  # Only these nonsecret values enter the container. No token, Docker socket or
  # host credential/home directory is exposed; the Lean mount is read-only.
  args=(docker run --rm --user "$(id -u):$(id -g)"
    --mount "type=bind,src=$PWD,dst=$PWD"
    --mount "type=bind,src=$toolchain_root,dst=/opt/lean,readonly"
    --workdir "$PWD"
    --env 'PATH=/opt/lean/bin:/usr/local/sbin:/usr/local/bin:/usr/sbin:/usr/bin:/sbin:/bin'
    --env 'HOME=/tmp/material-home'
    --env 'MATERIAL_EXECUTION_BACKEND=passed_container')
  for name in CI GITHUB_SHA GITHUB_REPOSITORY GITHUB_RUN_ID GITHUB_RUN_ATTEMPT \
      GITHUB_REF_NAME MATERIAL_JOBS LEAN_NUM_THREADS MATERIAL_COMMAND_TIMEOUT \
      MATERIAL_RESTORE_MODE MATERIAL_PARENT_IMAGE_DIGEST \
      MATERIAL_DEPENDENCY_CACHE_CLASS MATERIAL_PROJECT_CACHE_CLASS; do
    if [[ -v "$name" ]]; then args+=(--env "$name=${!name}"); fi
  done
  args+=("$MATERIAL_PARENT_IMAGE_DIGEST" /bin/bash -c
    'mkdir -p "$HOME"; exec python3 Material/ci/native_build.py --jobs "$MATERIAL_JOBS"')
  "${args[@]}"
else
  export MATERIAL_EXECUTION_BACKEND=native_host
  python3 Material/ci/native_build.py --jobs "$MATERIAL_JOBS" "${extra[@]}"
fi
