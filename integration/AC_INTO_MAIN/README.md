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

## Frozen boundary and live review

The first integration is pinned to the two revisions above. The merge commit is
`5a44e985c15a302110fd91d064431f1183e55857`, with both pinned commits retained as
parents. [Draft PR #2](https://github.com/randogelist/Methboke/pull/2) targets main.

AC advanced concurrently through `d884a36b` to `809aadc6`, adding the separate
`QFAHeatGenerator` candidate. That later research is outside this frozen merge.
It adds two active modules, one audit package and nine theorem targets; its
own acceptance and any later combined verification must retain separate source
identities. No pre-existing Lean file was changed by that observed AC delta.
The preserved integration remains the 654-module, 169-package, 2,212-name union.

The [independent static review](reviews/PRECOMMIT_STATIC_REVIEW.json) records
309 passing checks for the original prepared tree
`a7810ee179093a387f9740f94b544c735a886dfe`. It is a historical precommit review,
not a compiler receipt for a later documentation commit.

## Current acceptance

The combined source is **accepted at `5a44e985`**, by
[external run 44854389941](https://github.com/randogelist/Methboke/actions/runs/44854389941).
All **654 modules passed**: 548 compatible main-module reuses and 106 fresh
AC-only compilations. All **169 package audits ran fresh**, covering **2,212
named type/axiom reports**, followed by the fresh QFB cutout, full publication
and final Material acceptance. Every named type, axiom set and endpoint identity
from both accepted baselines is unchanged.

The [retained acceptance archive](../../audits/integration-5a44e985-accepted/README.md)
and [current status](INTEGRATION_STATUS.json) identify the exact source, report,
artifact digests and independent review. The original preparation report and
preservation manifest remain historical static records. The later ordinary
documentation commit receives its own external head check; it does not relabel
this accepted source receipt.

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

The full evidence must identify the actual tested source commit and run.
A documentation-only acceptance commit keeps that source identity in the
archive and receives its own ordinary external check. Its changes must preserve
all proof, audit, registration, pin, verifier and workflow inputs. The original
accepted-source archive remains authoritative for that run; a later green head
run is separate readiness evidence and does not require another documentation
commit merely to record another run.

Before any authorized promotion, re-read `main` and the reviewed PR head. If
`main` is still the pinned baseline, a non-force fast-forward to the reviewed
integration history preserves the original two-parent merge and both sources.
If repository policy uses a PR merge commit, retain that promotion identity
separately from the tested source. If main has advanced, first combine and
verify the newer changes on the integration branch. The task recorded here
prepares a reviewable branch; it does not advance main.

As part of a later authorized promotion, refresh the current working-branch and
completed-task selectors in GPT, README and status records for main. Keep the
original receipt's integration branch, tested commit and run immutable. Any
such edits remain documentation-only and follow the ordinary head-check rule.

The first ordinary main run after promotion establishes the combined cache in
main's own branch scope. GitHub's [cache access rules](https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching)
allow the current/default branch, and main cannot restore a cache created only
on its child integration branch. A compatible 548-module main donor may require
106 additions to be compiled externally before publication creates the combined
main snapshot. This is conditional on donor availability and receipts. Preserve
the existing single-donor validation and publication rules.

The final documentation commit uses an ordinary message so the current PR head
has its external check and a future normal main push can trigger verification.
GitHub [skip directives](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/skip-workflow-runs)
can suppress those workflows and leave required checks pending. No verification
requirement is waived for a documentation-only descendant.

If a later withdrawal is needed, use a reviewed ordinary revert while retaining
history and source-specific acceptance archives. The original integration has
main as parent 1; verify the actual promoted commit and its parent order before
choosing the mainline. A reverted merge remains in ancestry, so reintroducing
that same source requires an explicit restoration. Do not reset or force-push
main or delete accepted evidence and caches. A documentation-only problem calls
for a documentation correction.

[Detailed promotion review](reviews/PROMOTION_REVIEW.txt) records the observed
workflow, cache and history constraints. Later AC generator work remains a
separate, source-pinned follow-up under the same preservation and verification
requirements.
