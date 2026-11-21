# AC resources integrated with the accepted main resources

This branch combines the accepted FDSN work on `main` with the QFA/NSE-A
resources on `AC-Integration`. The project goal remains **Fefferman D**.
The immediate engineering task is to prepare and externally verify the combined
resource set. Advancing `main` is outside this branch-preparation task.

## Pinned inputs

| Role | Exact revision |
|---|---|
| Destination baseline, `main` | `4a609ea634ec4a5ff846049b9dc12b40b5f1a702` |
| Incoming baseline, `AC-Integration` | `000c1bd9baded808b79a04b7f666cacabce64939` |
| Common ancestor | `66a529248d3198ed70dc5489d82868bc33a37796` |
| Integration branch | `integration/ac-into-main` |

The integration commit retains both input commits as parents. The input branches
and their historical source/evidence identities are preserved.

## Current acceptance

The combined candidate is **pending matching external verification**.
See [INTEGRATION_STATUS.json](INTEGRATION_STATUS.json) for its current
source/run identity. The preparation report and source hash manifest establish
static preservation only; they are not compiler or kernel evidence.

The original main evidence retains these independent scopes:

- Direct Fefferman D: accepted at `66a5292`, with its isolated upstream
  Lean 4.34.0-rc2 environment.
- Periodic FDSN: accepted at `87ab6b4c`, with its original seed premise.
- FDSN_R3: accepted at `572fd9ee`, run
  [44848985720](https://github.com/randogelist/Methboke/actions/runs/44848985720),
  for the original `Seed -> Family` root and all sixteen endpoint scopes.

The incoming `000c1bd9` scope passed run
[44851575278](https://github.com/randogelist/Methboke/actions/runs/44851575278):
526 modules, 105 fresh package audits, 1,402 named type/axiom reports and the
fresh QFB cutout. Its [retained source-specific review](../../audits/material-000c1bd9-qfa-accepted/summary.json)
records compiler, archive, audit and publication identities. The most recent
35-name batch establishes the stated free-heat trajectory/time-energy and
every-window weighted-budget results. The general physical QFA/WFA roots remain
open; source integration does not promote them.

## Preservation and register union

All inherited Lean files retain their exact bytes. Existing namespaces, imports,
independent audit consumers, endpoint contracts and source-specific evidence are
preserved. The compiler, complete dependency lock, Lake configuration, native
verifier, cache policy and standalone QFB cutout retain their input identities.

The ten shared context/registration paths are reconciled using both branches'
evidence. The existing endpoint and owned-source entries common to the branches
are identical. Their union is:

| Inventory | Main | Incoming | Shared | Combined |
|---|---:|---:|---:|---:|
| Endpoint packages | 137 | 105 | 73 | 169 |
| Named type/axiom reports | 1,320 | 1,402 | 510 | 2,212 |
| Owned source modules | 142 | 119 | 78 | 183 |

The 304 retained vendor modules include two deliberately inactive upstream files.
Keeping those exclusions yields **654 active build modules**:
302 vendor modules, 183 owned modules and 169 endpoint wrappers. Compilation
continues to follow the registered import graph. Retained source snapshots and
historical cutouts are not automatically activated as build roots.

FDSN_R3's pointwise Fourier/Leray interface and AC's real L2/H1 interfaces remain
in their existing namespaces. Any mathematical bridge is a separate theorem,
not part of this integration.

Details: [PREPARATION_REPORT.json](PREPARATION_REPORT.json),
[PRESERVATION_MANIFEST.json](PRESERVATION_MANIFEST.json).

## External verification and cache behavior

The only workflow adjustment is adding `integration/ac-into-main` to the existing
Material push branch list. All verification commands, audit requirements,
resource limits and publication gates remain unchanged. No local Lean or Lake
execution is allowed.

The ordinary binary-cache path is used, with `exact_cache_benchmark=false` and
`force_rebuild=false`. Compatible existing objects may be reused. The current
verifier consumes one prior project report/snapshot; it does not combine two
branches' object caches. GitHub branch cache restrictions still apply after
source integration. Relative to a complete matching 548-module main donor,
106 modules are additional. Actual reuse depends on receipts and compilation
context, not this arithmetic alone.

The candidate must pass all 654 registered build modules, 169 fresh package
audits, 2,212 exact named type/axiom reports, the fresh QFB cutout, evidence
retention, publication, and the final `Material accepted` gate. The incoming
and main theorem type/axiom maps are compared with the candidate's reports.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.

Missing or incompatible external dependency objects are an obstruction. They
do not authorize local Lean execution or compilation of Mathlib from source.
Previous accepted evidence and cache snapshots are retained on failure.

## Review and possible later promotion

After matching acceptance, the branch's review should identify the exact tested
commit, compare the merged tree with both inputs and retain the complete fresh
audit evidence. Documentation-only acceptance updates must continue to identify
the actual tested source commit.

Any later promotion to `main` must recheck its current head. Prefer preserving
the reviewed integration commit and its history. If `main` has advanced, prepare
and verify the newly combined candidate; do not overwrite unrelated work.
Historical receipts are never relabeled with a different tested revision.

