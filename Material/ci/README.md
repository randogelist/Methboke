# Compiled endpoint container registry

`EXECUTION_ENVIRONMENT = external GitHub Actions / Linux amd64`.

`NO_LOCAL_LEAN = true` for repository preparation. This workflow is the separately requested external compilation path. Its result does not constitute a native Windows run.

## State transition

```text
push
  -> exact source checkout
  -> dependency/compiler/platform compatibility key
  -> last compatible PASSED container by registry digest
     OR cold pinned-toolchain bootstrap
  -> source overlay, preserving Lake objects/traces and prior audit evidence
  -> incremental build + exact type/axiom audit + no-op rerun measurement
  -> PASS report for this exact commit
  -> immutable aggregate container + immutable endpoint tags
  -> latest-compatible branch pointer, advancing along current branch ancestry
```

`FAIL -> evidence artifact; previous successful pointer unchanged`.

## Registry identities

Image repository: `ghcr.io/<owner>/<repository>-material`, lower-case.

| Identity | Form | Mutation policy |
|---|---|---|
| Successful aggregate | `passed-<commit12>-<run>-<attempt>` | New tag per successful run |
| Successful endpoint | `ep-<endpoint>-<inputhash12>-<run>-<attempt>` | New tag per successful endpoint/run |
| Reuse pointer | `latest-<branch>-<branchhash8>-<compatibility16>` | Updated after all endpoints PASS and forward-ancestry verification |

Endpoint tags refer to the aggregate image digest. Each endpoint retains its individual declaration, dependency and audit record; shared Lean/mathlib layers are not duplicated. No registry deletion or retention-pruning command is configured.

Every successful image contains the pinned toolchain, `/workspace/Material/.lake`, compiled endpoint sources, exact compiler/axiom logs and `/opt/material-registry/<run>-<attempt>.json`. The externally uploaded `registry-entry.json` records the pushed immutable image digest and endpoint tags.

## Incremental correctness

The compatibility key hashes the committed `lean-toolchain`, `lake-manifest.json`, Dockerfile and cache contract. Source amendments do not invalidate the whole container. Lake receives the amended source and preserves transitive dependency trace checks. The source overlay uses `rsync --checksum --no-times --omit-dir-times`; unchanged files retain their existing timestamps. Deleted sources are removed. Existing object files are never substituted for changed source without Lake's dependency validation.

Prior exact endpoint audit evidence is retained in `Material/registry/audits/` and the prior `current.json`. The build driver must validate its source/dependency/input hash before reusing an audit. Publication independently requires successful container exit, exact current commit, nonempty endpoint list and `PASS` for every endpoint.

Compatibility misses bootstrap the exact declared Lean toolchain. The build driver obtains the matching mathlib cache before compiling. A restored compatible PASSED image skips cache transfer only when the prior compiler/platform/pins match, every locked package has its expected clean source revision, and the requested Mathlib root objects/hash files/traces remain installed. Lake still validates the entire dependency DAG and the exact theorem audit remains mandatory. Missing prerequisites invoke the ordinary cache getter. The first successful run establishes the registry pointer; no successful image is assumed beforehand.

At the pinned mathlib revision, `Cache/Requests.lean:downloadFiles` filters via `Cache/IO.lean:ModuleHashMap.filterExists`, which checks `.ltar` archive presence rather than installed object presence. Therefore unconditionally running the cache getter after pruning archives would transfer the same closure again. The passed-output check avoids that warm-run transfer. Completed archives are pruned after PASS to limit image size and runner disk use; when outputs are missing or a new import is not installed, the fallback cache getter may redownload the required closure. This is an explicit storage/transfer tradeoff; proof checks remain unchanged.

## Runtime evidence

- `transport.json`: restore mode, previous image digest, bootstrap/restore seconds, container build/audit seconds.
- `current.json`: dependency and source changes, endpoint build/audit status and no-op rerun timing from the build driver.
- `registry-entry.json`: publication receipt and exact image digest.
- `image-optimization.json`: pruned completed `.ltar` archive count/bytes and warm-hydration policy.
- GitHub Actions artifact: all `Material/registry/` evidence, retained for 90 days independently of GHCR publication.

The secondary optimization target is measured runtime and reruntime, subject to identical theorem statements and axiom policy. No proof obligation or audit is removed to shorten runtime.

Initial/recovering local compilation is serialized in import-topological order with `lake build +Module:leanArts`, followed by the aggregate endpoint build and exact audits. `LEAN_NUM_THREADS` bounds Lean worker preference, not Lake's total compiler-process fan-out. A compatible previous PASS records local module source hashes; subsequent runs schedule changed/missing modules and their transitive dependents only. Aggregate Lake validation still executes, followed by one measured no-op rerun. This trades initial command-launch overhead for bounded local compilation concurrency.

Command stdout is streamed to the workflow and flushed to its evidence file while the process runs. Nonzero exits and timeouts retain partial output. `module_schedule` and serial/aggregate timings are recorded separately in `current.json`.

## Runner resource bounds

The build container receives at most two CPUs and a memory limit of `min(5 GiB, host total - 2 GiB, host available - 1 GiB)`, with no container swap and at most 512 processes. A minimum 2 GiB container budget is required. Preflight requires 20 GiB free disk before restore/bootstrap and 8 GiB before compilation. Before preflight, `prepare-runner.sh` reclaims only allowlisted unrelated Android/.NET/GHC SDK directories on disposable GitHub-hosted runners; developer and self-hosted machines are excluded. No workspace, Lean toolchain, registry image or Docker cache is removed. The first measured retry had only 12.59 GiB free and correctly stopped before compilation. Host and Docker resource snapshots are uploaded before compilation. During compilation, a 30-second monitor records host capacity and container usage; only this run's container is stopped if host free disk falls below 1 GiB or available memory below 256 MiB. Exit code, OOM status and resource aborts are recorded and prohibit publication.

## Credential and publication boundary

`GITHUB_TOKEN` remains on the runner host. The build container receives only a read-only source mount and nonsecret run identifiers; no Docker socket, credential directory or token is mounted or forwarded. `actions/checkout` disables persisted credentials.

Workflow events are `push` and manually authorized `workflow_dispatch`; no pull-request execution or publication path is configured. Permissions are `contents: read` and `packages: write`. Registry access or organization policy can still reject publication; in that case the compile/audit evidence remains available as a workflow artifact and the existing passed pointer remains valid.

A successful candidate may advance the pointer when the refreshed previous successful commit is its ancestor and the candidate is an ancestor of the current branch head. An absent pointer requires only the latter check. Thus, if `C2` is pushed while `C1` compiles, successful `C1` becomes available for the queued `C2` build. GitHub compare statuses `ahead` and `identical` certify the forward relation. An old rerun cannot replace a newer successful pointer; a divergent or force-pushed candidate cannot advance the current branch pointer. Concurrent runs of one branch are serialized, and the registry pointer is refreshed immediately before the ancestry checks. All branch names and tags are derived without shell interpolation.

## Verified upstream pins

- `actions/checkout@11d5960a326750d5838078e36cf38b85af677262` (`v4` inspected 2026-11-17).
- `actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02` (`v4`).
- elan `v4.2.4`, Linux x86_64 archive SHA256 `42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63`.
- Lean toolchain and all mathlib dependency revisions: committed Material lock files.

Primary documentation:

- https://docs.github.com/en/actions/tutorials/publish-packages/publish-docker-images
- https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry
- https://github.com/leanprover/elan/releases/tag/v4.2.4
- https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Cache/IO.lean#L267
- https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Cache/Requests.lean#L792
- https://github.com/leanprover/lean4/blob/v4.33.0/src/lake/Lake/Config/Module.lean#L119

## Local non-Lean validation

```bash
python3 -B -m unittest discover -s Material/ci/tests -p test_registry.py -v
bash -n Material/ci/container-build.sh
```

These checks mock Docker/network calls. They do not execute Lean, Lake, a compiler container or a theorem audit.
