# Cached verification and passed objects

The active workflow is `.github/workflows/material.yml`: Ubuntu 24.04,
Lean `leanprover/lean4:v4.33.0`, pinned Mathlib and the complete dependency lock.
Local authoring work never executes Lean. Linux evidence is not native Windows
verification. The first native binary-cache round passed at `66052f4`; automatic
recovery stopped on its first disk preflight; the **32 GiB repair awaits external CI**.

## Trial backends

Pushes and default manual runs use `binary_cache` during the pilot. Manual
`backend=registry` selects the existing GHCR path. `exact_cache_benchmark=true`
implies the binary backend and requires an exact project cache as well as exact
dependencies. Neither a prepared backend nor cache restoration establishes PASS.

The binary path restores separate Actions caches for `Material/.lake/packages`
and for own `.lake/build` outputs plus their previous `registry/current.json`.
An exact dependency hit, compatible project-cache match and prior PASS report
are required by the fast worker before compiler setup. Fast verification rejects
incomplete/incompatible installed dependency outputs; it does not fetch or rebuild
missing Mathlib objects. Ordinary binary runs allow compatible project prefixes
so amendments can reuse unchanged modules. An unsuccessful fast worker now leads
to the separate recovery worker described below, except in strict benchmark mode.

Compilation runs directly on the external native runner. Binary runs perform no
Docker authentication, pull, build or push, and do not advance the GHCR pointer.
The warm 20 GiB disk guard remains unchanged for fast comparison. Recovery
uses the cold disk guard with a step-local `MATERIAL_COLD_MIN_FREE_GIB=32`
override before a full project rebuild. The registry cold path remains at 40 GiB.
The bounded helper itself is unchanged. Existing passed GHCR
images and cache entries remain.

The first unchanged-source native round passed in 4m59s; an exact repeat and
comment amendment remain pending. The user's current scoped request adds automatic
recovery first. Agent work stops when CI starts; **go on** resumes inspection.

## Separate recovery runner

The workflow uses a shared local composite action for fast and recovery workers.
The fast job may fail; that alone never marks the whole workflow successful.
For ordinary binary runs, absence of its final `accepted` output starts a fresh
Ubuntu 24.04 recovery job at the same source SHA. Cancelled runs, strict
`exact_cache_benchmark=true` runs and the manual registry backend do not take this
path. A final verdict fails unless one worker supplies a fully accepted result.

Recovery skips all dependency/project Actions restoration and all Docker use.
It bootstraps the exact official Mathlib binary objects, rebuilds every current
own module, and runs every endpoint and cutout audit freshly. Its bundle guard
requires zero reused modules and a fresh PASS for the complete project plan.
If official dependency objects are unavailable, recovery fails; compiling Mathlib
from source is not a fallback. Proof sources, pins and module-identity drivers
remain unchanged.

After verification, recovery publishes a new binary artifact and append-only
`-recovered-<run>-<attempt>` dependency/project cache generations. It verifies
exact cache availability before acceptance. Ordinary fast runs first use
lookup-only probes for compatible recovered keys, avoiding a permanently broken
immutable canonical cache; strict benchmarks retain canonical exact-key rules.
Neither path removes previous good caches or images. Acceptance follows complete
verification, cache publication, archive upload and final evidence upload.

The first `[material-recovery-drill]` run,
[44085694998 at c461671](https://github.com/randogelist/Methboke/actions/runs/44085694998),
correctly started recovery and passed all 146 control tests plus source validation.
Its disk guard then failed before toolchain setup: 36,011,274,240 bytes
(33.54 GiB) remained after allowed SDK cleanup, below the inherited 40 GiB
requirement. No Lean or project build ran and no new package or caches were
published. The terminal acceptance gate correctly rejected the run.

Binary recovery now uses the helper's existing bounded 32 GiB minimum through
a step-local override; the Docker registry path retains 40 GiB. This changes
only resource admission, not the fresh-build or audit requirements. The next
`[material-recovery-drill]` push repeats recovery without deleting caches. Manual
`force_rebuild=true` supplies the same exercise. The completed full rebuild and
subsequent healed-cache reuse still require matching external evidence. A longer
full-project run is expected; it is not a warm benchmark.

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
`material-project-<shortSHA>-<run>-<attempt>-<fast|recovery>.tar.gz` with gzip level 1 and an adjacent `manifest.json`. It includes
receipt-verified own objects, `current.json` and required fresh audit logs;
it excludes Mathlib/dependency packages and stale unreceipted objects. The
manifest binds exact source/run/attempt, compiler/dependency identity, member
hashes, archive SHA256, bytes and packaging time. `binary-entry.json` records
`READY_FOR_UPLOAD`; successful remote upload is established by the Actions step.

Actions uploads `material-binary-<sha>-<run>-<attempt>-<fast|recovery>` with
**90-day retention**. Distinct worker names prevent partial primary publication
from colliding with recovery in the same run.
Own objects are also saved in the compatible project Actions cache. Dependencies
remain in their separate cache. Actions caches are the restoration input; an
expired binary artifact alone does not block reuse while those caches remain.
When cached inputs are missing or unusable, recovery recreates caches and a fresh
project archive. This is not a durable dependency-release backup, and standalone
archive restoration has not been exercised. No compiled binary is committed into
Git. Verified
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

## Verified comparison baselines

[Native binary run 44080437531](https://github.com/randogelist/Methboke/actions/runs/44080437531)
at `66052f498614c8b3dc31f5331f5bfdd4667fa87c` passed in **4m59s**, excluding
queue: 283 reused objects, zero fresh modules, all fourteen endpoint audits and
the cutout fresh, and 139 control tests passed. Cleanup took 43s, dependency cache
restoration 66s, own cache restoration 2s, compiler setup 18s, verification 137s,
packaging 8s and upload 3s. Driver time was 128.521s, including 96.004s fresh audits.
The project archive is 25,391,076 bytes; separate compressed Actions caches are
19,904,940 bytes for own objects and 2,527,746,970 bytes for dependencies. All
299 archive member hashes and 283 module receipts were checked against
[matching evidence](https://github.com/randogelist/Methboke/actions/runs/44080437531/artifacts/14327621291).
This verifies warm native reuse and archive publication, not the prepared recovery
worker or a durable archive-download fallback. No Docker operations occurred.


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

The 139 control tests passed in external round 1; all 146, including the seven
bundle recovery tests, passed in the first recovery drill. One additional mocked
regression covers the observed disk availability under the 32/40 GiB profiles
(147 total expected on the next external run).
No project tests or Lean commands are executed locally.
