# Passed endpoint registry

`current.json`: exact source commit, compiler/platform, dependency identity, per-endpoint type/axiom evidence, cache reuse and timings.

`registry-entry.json`: successful container identity, parent digest, immutable aggregate tag and immutable endpoint tags.

`registry-entry.json` additionally records the published digest and pointer update result after publication succeeds.

`transport.json`: restore/bootstrap and container execution result, including failures.

`logs/`: cache hydration, compiler version, initial build and no-op rerun logs.

`audits/`: content-addressed exact type and theorem-level axiom logs eligible for validated reuse.

`/opt/material-registry/` inside passed images: immutable successful container records. Previous full reports remain available in their immutable predecessor images.

Generated evidence is retained by GHCR images and GitHub Actions artifacts. A source manifest or an empty registry is not PASS evidence.
