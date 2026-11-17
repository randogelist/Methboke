# Native cached verification and passed snapshots

The active workflow is `.github/workflows/material.yml`: native Ubuntu 24.04,
Lean `leanprover/lean4:v4.33.0`, pinned Mathlib and complete dependency lock.
The first seed runs natively on the host; later registry-restored builds execute
inside the exact last passed image.
Local authoring validation never executes Lean. Linux evidence is not native
Windows evidence.

On a push to `main`, CI restores the latest compatible passed GHCR snapshot by
immutable digest. Its dependency and project objects are restored into the
current workspace. That amended workspace is then mounted into the same passed
image, which internally compiles only affected own modules and freshly audits
all endpoints. If there is no accessible snapshot, independent compatible Actions caches
are restored. A first seed uses the pinned official Mathlib cache and compiles
only the requested own-source closure. The build driver never issues a Mathlib
source build. Missing official objects fail elaboration instead of authorizing a
source rebuild. Actions caches from Methlib cannot be restored directly in this
repository; the first Methboke seed is reported as a miss.

After installing the pinned compiler, CI checks all audit `set_option` lines in
an isolated Lean probe before compiling project modules. This catches printer
option incompatibilities early; it does not count as a theorem audit or PASS.
The full endpoint and cutout audits still run after compilation.

`native_build.py` implements the QFB dependency-frontier pattern with `--jobs 2`.
`LEAN_NUM_THREADS=2` is a separate compiler setting. Module reuse requires a
matching compiler, dependency lock, platform, configuration/policy, all installed
external `.olean*` hashes, source hash, recursively imported own-object identities,
and every retained object/companion digest. Only affected own modules are rebuilt.
Independent modules run concurrently; a failed module blocks its dependants while
unrelated modules continue. Each verification freshly elaborates all fourteen
audit files (41 configured declaration entries) and the single-file original QFB
cutout. The cutout repeats the same QFB theorem; it is not an additional distinct
mathematical result. Old audit logs never satisfy a new run.

The source/configuration receipt adapter has compiler-free adversarial tests and
follows the established QFB reuse contract. The selected package passed at
`6440270`; each later amendment still needs matching external evidence. New
snapshot publication tests are prepared for external CI only. No CI-green claim
is made from Python tests or local static inspection.

## Exact-cache benchmark

The manual `exact_cache_benchmark` input selects the H12-style measurement:
exact dependency and project Actions-cache hits are mandatory. A miss ends the
measurement before compiler setup. The ordinary push profile can seed missing
own objects and retrieve official dependency objects. It never labels a miss
as a warm run. Every actual verification performs fresh required audits.

`current.json` reports compiler identity, execution backend, dependency revisions, module counts,
fresh/reused physical source lines, build/audit time, and receipt-recheck time.
The secondary no-op measurement checks all source/object receipts again; it is
explicitly **not** a second Lean compilation or duplicate theorem audit.
`run-plan.json` records the exact source, pins, endpoint scope, policy and controls
before external Lean execution. `transport.json` records restoration and native
exit status. Compatible registry restoration records dependency cache class EXACT
and project class PREFIX; the restore mode separately identifies the registry,
and per-module receipts establish which objects actually match. Missing setup/upload measurements remain in Actions step timings;
no stable-runtime guarantee is inferred from a single run.

## Passed registry

The image repository is `ghcr.io/<owner>/<repository>-material`. Images are
runnable Ubuntu 24.04 snapshots, published only after compilation and all fresh
audits pass. They include copied sources, dependency/project objects, receipts
and audit evidence. Image construction executes no Lean compiler. On the next
registry-restored push, `verify-external.sh` invokes that exact immutable image
and runs the amendment build inside it. The same checksum-pinned host-installed
Lean toolchain is mounted read-only at `/opt/lean`; it is not duplicated inside
the image. The current workspace is mounted at its original absolute path, and
the container uses the runner UID/GID. Only explicit nonsecret run/cache settings
are forwarded. No token, Docker socket or host credential directory is mounted.
Cold seeding, Actions-cache fallback and exact-cache benchmarks use the native
host. Both paths share the identical receipt scheduler and fresh audit policy.

| Registry identity | Meaning |
|---|---|
| `passed-<commit12>-<run>-<attempt>` | Immutable successful aggregate snapshot |
| `ep-<endpoint>-<inputhash12>-<run>-<attempt>` | Endpoint tag referencing the same aggregate bytes |
| `latest-<branch>-<branchhash8>-<compatibility16>` | Compatible latest successful branch pointer |

The pointer advances only if `previous successful commit <= candidate <= current
branch head`. Old reruns cannot replace newer successful pointers. Failed builds,
missing audits, unapproved axioms or snapshot publication failures leave the last
passed pointer intact. Verified compiler/audit evidence is uploaded before
publication; final diagnostics are uploaded afterward. Generic Actions caches
are saved only after the current native build and fresh audits pass. Registry
hits skip the redundant dependency archive save. Publication has a 15-minute
step timeout.

Compatibility hashes the toolchain, full lock, Lake configuration, snapshot
Dockerfile and cache contract. Source and audit-policy changes also affect the
project cache key and module receipts. Reuse never crosses Linux/Windows or Lean
version boundaries. Registry/source identifiers are passed as structured process
arguments. Credentials are scoped to registry login/publication steps; checkout
does not retain credentials.

`registry.py`, `Dockerfile` and `container-build.sh` retain the historical container
backend for review/replay. The active main workflow uses `native_registry.py`, `verify-external.sh` and
`Snapshot.Dockerfile`. Its existing ancestry and PASS publication gates are shared
with the historical implementation.

## Warm snapshot disk repair

Run `44059698760` restored the passed image in 264s and completed the verification
step in 157s, according to GitHub job summaries. Its full snapshot publication
then copied a 7.67 GB context and exhausted disk. The matching artifact was not
available, so no exact module-reuse count or new theorem receipt is asserted.
The later comment run reached the same publication stage after a successful
162s verification step. The original `6440270` passed snapshot remains the base.

The prepared repair generates a warm Dockerfile FROM the validated immutable
parent digest. It retains `.lake/packages` in the inherited image layer, removes
old own sources/outputs, and copies current Material sources, all own build
outputs, cutouts and fresh evidence. The staged context excludes the dependency
directory. Inheritance requires matching compiler/toolchain, pins, platform,
retained passed-cache status and external `.olean*` digest. This digest covers
Lean object files and their `.olean*` companions, not every IR or trace file.
A dependency mismatch fails closed rather than silently copying an oversized
replacement into the warm image. The original cold `Snapshot.Dockerfile` and
its compatibility identity stay unchanged.

Context size and available disk are recorded before construction; a proportional
headroom check stops unsafe publication before the runner fills. Compatible
caches and parent images are not pruned. This repair is
`PENDING_EXTERNAL_VERIFICATION`; prepared code is not a passed publication.
Repeated parent-image layering may eventually require a bounded dependency-base
strategy; that longer-term optimization is not part of this repair.

The scoped recovery workflow targets only obsolete run `44061664660`, checks
its exact commit and workflow identity, requests ordinary cancellation, and
uses force cancellation if it remains active. The user explicitly authorized
cancellation of such stalled runs. It does not delete registry images.

## Reference configurations

| Source | Verified observation | Adopted structure |
|---|---|---|
| [Methlib QFB run 43801307847](https://github.com/randogelist/Methlib/actions/runs/43801307847) | 4m40, 74/74 objects reused | Two-worker dependency scheduler and fresh audits |
| [Methlib H12 run 43361151038](https://github.com/randogelist/Methlib/actions/runs/43361151038) | 3m03, sixteen checkpoints | Separate dependency/project restoration and exact-cache measurement |

These timings have different target scopes from Material's 269 inherited modules
plus fourteen wrappers. They are structural references, not predicted runtimes.

## Compiler-free preparation checks

```bash
python3 -m unittest discover -s Material/ci/tests
python3 Material/ci/build.py --validate-only
```

These checks cannot establish a Lean theorem or unconditional finite-cap closure.
