# Passed endpoint evidence and object registry

This directory holds generated external verification and publication evidence.
Prepared sources or an empty registry do not establish a compiler pass.

The latest accepted GHCR baseline is
[run 44073883524, attempt 2](https://github.com/randogelist/Methboke/actions/runs/44073883524/attempts/2),
source `68e9f8ad8663ebfcc0b84ca5b927908dfe5e1602`. Its immutable image is:

```text
ghcr.io/randogelist/methboke-material@sha256:c9263b3679086bc2874e1cd5ecaa721be41a02d28dfbf1abea070bb9a2d17ba4
```

All 283 objects were reused; fourteen endpoint audit files covering 41
declarations and the QFB cutout passed freshly. The job took 8m13s, and all 125
control tests passed. The aggregate/endpoint tags and compatible main pointer
were published. [Matching evidence](https://github.com/randogelist/Methboke/actions/runs/44073883524/artifacts/14324548770)
has checked ZIP, report and all fifteen fresh audit-log hashes. Earlier accepted
baselines remain separately retained. This is not native binary-pilot acceptance.

The prepared pilot defaults to the `binary_cache` backend: separate existing
Actions caches restore dependencies and own objects, the native runner compiles
amendments, and every required audit remains fresh. Exact dependency restoration,
compatible project objects and a prior PASS report are mandatory. No Docker
publication occurs and the existing GHCR pointer is preserved. Manual
`backend=registry` retains the previous container path.

After complete verification, the pilot prepares `material-project-<shortSHA>-<run>-<attempt>.tar.gz`, a
hashed manifest and `binary-entry.json`. The archive contains current
receipt-verified own `.olean*` objects and fresh evidence, not dependency packages.
Actions retains it as `material-binary-<sha>-<run>-<attempt>` for **90 days**;
dependencies remain in their separate cache. This is a pilot archive, not a
durable dependency-release fallback. Artifact preparation and successful remote
upload are distinct states. No generated PASS record is committed to simulate
verification of a prepared configuration.

- `current.json`: exact tested source, compiler/platform/dependencies, endpoint
  acceptance, object reuse and driver timings.
- `binary-entry.json`: verified project archive identity and upload preparation.
- `registry-entry.json`: GHCR snapshot digest, aggregate/endpoint aliases and
  pointer update for the registry backend.
- `transport.json` and other diagnostics: backend, restoration, infrastructure
  state and failures; these alone are not theorem acceptance.
- `logs/` and `audits/`: fresh compiler, exact-type and axiom evidence. Prior
  logs cannot satisfy a new run's audit requirement.

Every accepted artifact must bind a successful current build and all fresh
audits to the exact source, compiler, dependency and object identities. Private
storage controls access; it does not replace these checks. The
[CI controls](../ci/README.md) describe backend selection and the planned three
rounds. Agent work stops once each external runner starts.
