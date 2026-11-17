# Cached verification and passed objects

The active workflow is `.github/workflows/material.yml`: Ubuntu 24.04,
Lean `leanprover/lean4:v4.33.0`, pinned Mathlib and the complete dependency lock.
Local authoring work never executes Lean. Linux evidence is not native Windows
verification. The native binary-cache trial is **prepared, pending external CI**.

## Trial backends

Pushes and default manual runs use `binary_cache` during the pilot. Manual
`backend=registry` selects the existing GHCR path. `exact_cache_benchmark=true`
implies the binary backend and requires an exact project cache as well as exact
dependencies. Neither a prepared backend nor cache restoration establishes PASS.

The binary path restores separate Actions caches for `Material/.lake/packages`
and for own `.lake/build` outputs plus their previous `registry/current.json`.
An exact dependency hit, compatible project-cache match and prior PASS report
are required before compiler setup. A miss stops the trial honestly. Native
verification also rejects incomplete/incompatible installed dependency outputs;
it does not fetch or rebuild missing Mathlib objects. The ordinary binary round
allows compatible project prefixes so amendments can reuse unchanged modules.

Compilation runs directly on the external native runner. Binary runs perform no
Docker authentication, pull, build or push, and do not advance the GHCR pointer.
The warm 20 GiB disk guard remains unchanged for comparison; the 40 GiB cold-seed
cleanup is excluded. Existing passed GHCR images and dependency caches remain.

The planned rounds are (1) unchanged-source native reuse, (2) an exact repeat,
and (3) a comment amendment. Each round starts only within the user's continuing
work; agent work stops when CI starts, and **go on** resumes inspection. Faster
runtime is a hypothesis, not a preparation result.

## Shared verification contract

`native_build.py` uses two dependency-frontier workers; `LEAN_NUM_THREADS=2` is
a separate compiler setting. Reuse requires matching compiler, lock, platform,
configuration/policy, installed external `.olean*` digest, source hash, recursive
own-import identities and every retained object/companion hash. Only affected
own modules rebuild. The driver, launcher, pins and proof sources are unchanged
for this trial, preserving compatible per-module receipts.

Every verification freshly elaborates all fourteen endpoint audit files,
covering 41 declaration entries, plus the original QFB single-file cutout.
Exact types and allowed axioms are checked against fresh logs. The cutout repeats
the original root; it is not an extra mathematical result. The early printer
option probe detects unsupported audit options but is not theorem acceptance.

`current.json` records compiler/dependencies, execution backend, source, reuse
counts and timings. `run-plan.json` records scope and controls before compiler
execution. The receipt recheck is explicitly not another Lean pass. Restoration
metadata and Actions step timings distinguish cache hits, setup, compilation,
audits, archive publication and failed phases.

## Binary pilot archives

After the native build and all fresh audits pass, `binary_bundle.py` revalidates
the current evidence and own `.olean*` receipts, then prepares
`material-project-<shortSHA>-<run>-<attempt>.tar.gz` with gzip level 1 and an adjacent `manifest.json`. It includes
receipt-verified own objects, `current.json` and required fresh audit logs;
it excludes Mathlib/dependency packages and stale unreceipted objects. The
manifest binds exact source/run/attempt, compiler/dependency identity, member
hashes, archive SHA256, bytes and packaging time. `binary-entry.json` records
`READY_FOR_UPLOAD`; successful remote upload is established by the Actions step.

Actions uploads `material-binary-<sha>-<run>-<attempt>` with **90-day retention**.
Own objects are also saved in the compatible project Actions cache. Dependencies
remain in their separate cache. This is a pilot archive, not a durable release
fallback for dependencies. No compiled binary is committed into Git. Verified
compiler/audit evidence is uploaded before publication, and final diagnostics
are uploaded even when publication fails.

## GHCR alternative

The `registry` backend restores the exact compatible passed image by digest.
`container_workspace.py` keeps dependencies and own objects inside it, overlays
current source at `/workspace`, and exports only fresh evidence and verified own
outputs. The pinned host Lean installation is mounted read-only at `/opt/lean`.
No host workspace, credentials, home directory or Docker socket is mounted.

Successful GHCR publication creates the aggregate
`passed-<commit12>-<run>-<attempt>`, fourteen endpoint aliases and a compatible
latest-pass pointer. The pointer advances only within the current compatible
branch ancestry. Each warm snapshot inherits dependencies from its authenticated
parent and replaces own sources/outputs/evidence. Context size and disk headroom
are checked. Failed verification/publication leaves previous passed images intact.
A registry miss may use compatible caches or the exact official dependency cache;
Mathlib source compilation is never authorized. Its cold snapshot recipe remains.

## Verified comparison baseline

[Run 44073883524, attempt 2](https://github.com/randogelist/Methboke/actions/runs/44073883524/attempts/2)
at `68e9f8ad8663ebfcc0b84ca5b927908dfe5e1602` passed in **8m13s**, excluding
queue: all 283 own objects reused; all fourteen endpoint audits and the cutout
fresh; 125 control tests passed. Cleanup took 78s, image restoration 160s,
compiler installation 17s, verification 151s and publication 70s. Driver time
was 133.550s: cache 29.880s, own build 0.464s and fresh audits 101.865s.
[Matching evidence](https://github.com/randogelist/Methboke/actions/runs/44073883524/artifacts/14324548770)
has verified archive/report/audit-log hashes. This measures GHCR, not binary CI.

The preceding comment amendment passed in 9m08s with 282 reused objects and one
rebuilt wrapper. Earlier unchanged-source `04fbd79` passed in 7m26s; `73c2e98`
passed in 8m07s. Variable cleanup/import/transfer times prevent a speed guarantee.
The old 7.67 GB Docker-context failure remains historical infrastructure evidence.
The current small context is not a measurement of total image size.

Reference designs remain the Methlib QFB 4m40s / 74-object reuse run and H12
3m03s / sixteen-checkpoint run. Their scopes differ from this project's 283
modules. Source preparation, Python control tests and static inspection cannot
establish a new Lean theorem or unconditional finite-cap closure.

Fourteen additional control tests are prepared for external CI (139 total expected).
They have not been executed locally.
