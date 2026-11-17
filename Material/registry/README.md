# Passed endpoint registry

This directory holds generated external verification and publication evidence.
Source preparation or an empty registry does not establish a compiler pass.

- `current.json` records the tested commit, compiler/platform/dependency
  identity, endpoint acceptance, reuse and timing data.
- `registry-entry.json` records a successfully published snapshot, its immutable
  aggregate/per-endpoint tags, digest and passed-pointer update result.
- Transport/resource diagnostics record restoration and infrastructure outcomes,
  including failures. Their success is not theorem acceptance.
- `logs/` and `audits/` retain compiler and exact declaration/type/axiom evidence.
  Each new verification executes all required audits freshly; historical audit
  logs are not reused as the new run's acceptance.

The first seed uses the external native runner. Subsequent commits execute
amendments inside the exact last passed GHCR container, with compatible objects,
the current source and a read-only pinned compiler mount. Publication
requires the exact current source identity and a complete successful build and
fresh audit. Immutable prior passes remain available even when an amendment
fails. A latest-pass pointer advances only within its compatible ancestry.

GitHub Actions artifacts preserve evidence independently of registry publication.
The workflow's [CI controls](../ci/README.md) specify filenames, compatibility
checks and publication gates. No generated PASS receipt is committed merely to
represent a prepared configuration.
