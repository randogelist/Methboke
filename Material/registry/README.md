# Passed endpoint registry

This directory holds generated external verification and publication evidence.
Source preparation or an empty registry does not establish a compiler pass.

The first accepted snapshot is from [run 44052579373](https://github.com/randogelist/Methboke/actions/runs/44052579373),
source `6440270ffe9b05b2956cd34c59c65f2fe341e8b8`. Its immutable image is:

```text
ghcr.io/randogelist/methboke-material@sha256:faadfe0f93ebda8ae9bbb34f5f632456400e25197b4636fb5436a86afbe90f1d
```

The aggregate tag and 14 endpoint tags were published, and the compatible main
pointer was updated. [Retained evidence](../../audits/material-6440270/summary.json)
contains the exact report, publication record and fresh audit logs. This remains
the last fully accepted and published snapshot. Warm run `44059698760` restored
it and passed the verification step, then exhausted disk during publication.
Its matching artifact is unavailable; step success alone does not replace the
source-specific theorem receipts.

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

Warm publication now has a prepared path that inherits `.lake/packages` from
the exact immutable parent after matching its compiler, pins, retained-cache
status and external `.olean*` digest. Its context contains current sources, all
own outputs, cutouts and fresh evidence; old own sources and outputs are replaced.
Disk headroom and context size are recorded before Docker construction. The
original full cold-seed recipe and prior passed images are preserved. This
repair is pending external verification.

GitHub Actions uploads verified evidence before registry publication, then
uploads final publication diagnostics separately. This preserves compiler
evidence if subsequent image construction fails.
The workflow's [CI controls](../ci/README.md) specify filenames, compatibility
checks and publication gates. No generated PASS receipt is committed merely to
represent a prepared configuration.
