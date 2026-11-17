# Passed endpoint registry

`current.json`: exact source commit, compiler/platform, dependency identity, per-endpoint type/axiom evidence, cache reuse and timings.

`registry-entry.json`: successful container identity, parent digest, immutable aggregate tag and immutable endpoint tags.

`registry-entry.json` additionally records the published digest and pointer update result after publication succeeds.

`transport.json`: restore/bootstrap and container execution result, including failures.

`logs/`: compiler, cache, exact type and theorem-level axiom logs.

`history/`: prior successful run records retained inside passed containers.

Generated evidence is retained by GHCR images and GitHub Actions artifacts. A source manifest or an empty registry is not PASS evidence.
