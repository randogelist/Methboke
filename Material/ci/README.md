# Native cached verification and passed snapshots

The active workflow is `.github/workflows/material.yml`: native Ubuntu 24.04,
Lean `leanprover/lean4:v4.33.0`, pinned Mathlib and complete dependency lock.
The first seed runs natively on the host; later registry-restored builds execute
inside the exact last passed image.
Local authoring validation never executes Lean. Linux evidence is not native
Windows evidence.

On a push to `main`, CI restores the latest compatible passed GHCR snapshot by
immutable digest. The prepared `container_workspace.py` path keeps inherited
dependency and own objects inside that image instead of copying the full cache
to the host. It overlays current Material source and cutouts at `/workspace`,
runs the unchanged compiler/audit driver, and exports only fresh registry
evidence and successful own build outputs. Each exported object is checked
against its receipt before acceptance. This workspace optimization is pending
external verification; the preceding mounted-workspace path passed at `73c2e98`.

If no compatible registry snapshot is available, independent compatible Actions
caches are restored and the native-host path is used. A first seed uses the
pinned official Mathlib cache and compiles only the requested own-source closure.
The driver never issues a Mathlib source build. Missing official objects fail
elaboration instead of authorizing a source rebuild. Actions caches from Methlib
cannot be restored directly in this repository.

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
`6440270` and `73c2e98`; each later amendment still needs matching external
evidence. The latter run passed all 100 external control tests. New workspace
and cleanup tests are prepared for external CI only. Python tests or local
static inspection alone cannot establish a Lean theorem.

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
registry-restored push, the prepared `container_workspace.py` launches that exact
immutable image and runs the amendment build at `/workspace`. The checksum-pinned
host Lean toolchain is mounted read-only at `/opt/lean`; it is not duplicated
inside the image. Source is copied into the isolated container without mounting
the host workspace, home, credentials or Docker socket. Only explicit nonsecret
run/cache settings are forwarded. The container uses its root identity to read
and write its own inherited files without changing dependency ownership.

Cold seeding, Actions-cache fallback and exact-cache benchmarks use the native
host through `verify-external.sh`. Both paths retain the same source/compiler
receipt scheduler and fresh audit policy. The new transport source hash is
recorded separately, without weakening compiled-object identity checks.

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
backend for review/replay. The active main workflow uses `native_registry.py`,
`container_workspace.py`, native fallback `verify-external.sh`, and the snapshot
recipes. Its existing ancestry and PASS publication gates are shared
with the historical implementation.

## Verified warm publication and next optimization

Earlier run `44059698760` restored the passed image and completed verification,
then exhausted disk while copying a 7.67 GB context. Its matching audit artifact
was unavailable, so no exact reuse count or new theorem receipt is asserted.
The corrected [run 44066821232](https://github.com/randogelist/Methboke/actions/runs/44066821232) passed at
`73c2e98`: 282/283 own objects reused, one comment-modified endpoint rebuilt,
all 14 endpoint audits plus cutout fresh, and publication complete. Job 8m07s
excludes queue time; restoration took 212s, SDK cleanup 48s, verification step
141s and publication 55s. Exact evidence is retained under
[material-73c2e98](../../audits/material-73c2e98/summary.json).

Warm publication inherits `.lake/packages` from the validated immutable parent.
The new layer replaces current sources, own outputs and fresh evidence; its
73,327,527-byte context excludes the large dependency directory. Inheritance
requires matching compiler/toolchain, pins, platform, retained-cache status and
external `.olean*` digest. That digest covers Lean objects and their `.olean*`
companions, not every IR/trace file. A mismatch fails closed. The original cold
`Snapshot.Dockerfile` and compatibility identity remain unchanged. Context size
and disk headroom are checked before construction; no passed image is pruned.

The next optimization removes the remaining full dependency export during
restoration and verifies hashes on the smaller exported own-object set. It is
`PREPARED_PENDING_EXTERNAL_VERIFICATION`, not an already measured improvement.
Repeated parent-image layering may eventually require a bounded dependency-base
strategy; that separate optimization is not part of this change.

SDK cleanup first checks a bounded free-space target and stops after reaching
it. Defaults are 20 GiB before warm restoration and 40 GiB for the cold-seed path;
configuration may adjust these only within the implementation's allowed bounds.
Deletion is restricted to the existing unrelated SDK allowlist on disposable
GitHub-hosted runners. Workspace, toolchain, caches and images are excluded.
Per-mode reports record the budget, space observations and cleanup decisions.

The historical recovery workflow targets only obsolete run `44061664660`, checks
its exact commit/workflow identity and requests cancellation, escalating to
force cancellation when needed. It does not delete registry images.

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
