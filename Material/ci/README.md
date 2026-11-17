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
  -> latest-compatible branch pointer, only when commit remains branch HEAD
```

`FAIL -> evidence artifact; previous successful pointer unchanged`.

## Registry identities

Image repository: `ghcr.io/<owner>/<repository>-material`, lower-case.

| Identity | Form | Mutation policy |
|---|---|---|
| Successful aggregate | `passed-<commit12>-<run>-<attempt>` | New tag per successful run |
| Successful endpoint | `ep-<endpoint>-<inputhash12>-<run>-<attempt>` | New tag per successful endpoint/run |
| Reuse pointer | `latest-<branch>-<branchhash8>-<compatibility16>` | Updated only after all endpoints PASS and current-head verification |

Endpoint tags refer to the aggregate image digest. Each endpoint retains its individual declaration, dependency and audit record; shared Lean/mathlib layers are not duplicated. No registry deletion or retention-pruning command is configured.

Every successful image contains the pinned toolchain, `/workspace/Material/.lake`, compiled endpoint sources, exact compiler/axiom logs and `/opt/material-registry/<run>-<attempt>.json`. The externally uploaded `registry-entry.json` records the pushed immutable image digest and endpoint tags.

## Incremental correctness

The compatibility key hashes the committed `lean-toolchain`, `lake-manifest.json`, Dockerfile and cache contract. Source amendments do not invalidate the whole container. Lake receives the amended source and preserves transitive dependency trace checks. The source overlay uses `rsync --checksum --no-times --omit-dir-times`; unchanged files retain their existing timestamps. Deleted sources are removed. Existing object files are never substituted for changed source without Lake's dependency validation.

Prior exact endpoint audit evidence is retained in `Material/registry/audits/` and the prior `current.json`. The build driver must validate its source/dependency/input hash before reusing an audit. Publication independently requires successful container exit, exact current commit, nonempty endpoint list and `PASS` for every endpoint.

Compatibility misses bootstrap the exact declared Lean toolchain. The build driver obtains the matching mathlib cache before compiling. The first successful run establishes the registry pointer; no successful image is assumed beforehand.

## Runtime evidence

- `transport.json`: restore mode, previous image digest, bootstrap/restore seconds, container build/audit seconds.
- `current.json`: dependency and source changes, endpoint build/audit status and no-op rerun timing from the build driver.
- `registry-entry.json`: publication receipt and exact image digest.
- `image-optimization.json`: removed completed `.ltar` download count/bytes; installed objects and dependency source retained.
- GitHub Actions artifact: all `Material/registry/` evidence, retained for 90 days independently of GHCR publication.

The secondary optimization target is measured runtime and reruntime, subject to identical theorem statements and axiom policy. No proof obligation or audit is removed to shorten runtime.

## Credential and publication boundary

`GITHUB_TOKEN` remains on the runner host. The build container receives only a read-only source mount and nonsecret run identifiers; no Docker socket, credential directory or token is mounted or forwarded. `actions/checkout` disables persisted credentials.

Workflow events are `push` and manually authorized `workflow_dispatch`; no pull-request execution or publication path is configured. Permissions are `contents: read` and `packages: write`. Registry access or organization policy can still reject publication; in that case the compile/audit evidence remains available as a workflow artifact and the existing passed pointer remains valid.

An old successful rerun keeps its immutable successful tags but cannot overwrite the current branch pointer. Concurrent runs of one branch are serialized. All branch names and tags are derived without shell interpolation.

## Verified upstream pins

- `actions/checkout@11d5960a326750d5838078e36cf38b85af677262` (`v4` inspected 2026-11-17).
- `actions/upload-artifact@ea165f8d65b6e75b540449e92b4886f43607fa02` (`v4`).
- elan `v4.2.4`, Linux x86_64 archive SHA256 `42b94d4244e8353142c456ec0e4ca6528fd898a6c604d4059f494e706e431f63`.
- Lean toolchain and all mathlib dependency revisions: committed Material lock files.

Primary documentation:

- https://docs.github.com/en/actions/tutorials/publish-packages/publish-docker-images
- https://docs.github.com/en/packages/working-with-a-github-packages-registry/working-with-the-container-registry
- https://github.com/leanprover/elan/releases/tag/v4.2.4

## Local non-Lean validation

```bash
python3 -B -m unittest discover -s Material/ci/tests -p test_registry.py -v
bash -n Material/ci/container-build.sh
```

These checks mock Docker/network calls. They do not execute Lean, Lake, a compiler container or a theorem audit.
