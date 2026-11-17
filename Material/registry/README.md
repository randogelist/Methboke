# Passed endpoint registry

This directory holds generated external verification and publication evidence.
Source preparation or an empty registry does not establish a compiler pass.

The latest accepted snapshot is from [run 44066821232](https://github.com/randogelist/Methboke/actions/runs/44066821232),
source `73c2e98e68b4f2f53a7de4d0be622e5739066fc3`. Its immutable image is:

```text
ghcr.io/randogelist/methboke-material@sha256:f5e043ed22085029f59aa7ca76d63cb01d4b43d109304bcce54e21584e03245a
```

The aggregate tag and 14 endpoint tags were published, and the compatible main
pointer was updated. [Retained evidence](../../audits/material-73c2e98/summary.json)
contains the exact report, publication record and fresh audit logs: 282/283 own
objects reused, one rebuilt, all endpoint/cutout audits fresh, job 8m07s excluding
queue. The first cold baseline at `6440270` remains retained separately.

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

Warm publication inherits `.lake/packages` from the exact immutable parent
after matching its compiler, pins, retained-cache status and external `.olean*`
digest. Its context contains current sources, all own outputs, cutouts and fresh
evidence; old own sources and outputs are replaced. This path passed at
`73c2e98`, with a 73.42 MB context and 55s publication step. Disk headroom is
checked before Docker construction; the cold recipe and prior images remain.

The next container-native workspace optimization is prepared, not yet accepted.
It leaves inherited dependencies inside the running image and exports only own
outputs and evidence; every exported object must match its current receipt.
Publication still requires all fresh audits and the exact source identity.

GitHub Actions uploads verified evidence before registry publication, then
uploads final publication diagnostics separately. This preserves compiler
evidence if subsequent image construction fails.
The workflow's [CI controls](../ci/README.md) specify filenames, compatibility
checks and publication gates. No generated PASS receipt is committed merely to
represent a prepared configuration.
