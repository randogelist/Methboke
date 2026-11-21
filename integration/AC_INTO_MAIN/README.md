# AC resources integrated with the accepted main resources

The completed integration combines the accepted FDSN work on `main` with the QFA/NSE-A
resources on `AC-Integration`. The project goal remains **Fefferman D**.
The user authorized promotion after exact head verification. Main was advanced
by non-force fast-forward to `e627a39e6c27cd4432ab063741fe726af8378a63` on
2026-11-21 at 02:46:09 UTC, and PR #2 is closed and merged. The integration
target is `MERGED_COMPLETE`. Main verification and publication of the combined
cache have passed. Only the later documentation-head external check remains.

## Pinned inputs

| Role | Exact revision |
|---|---|
| Destination baseline, `main` | `4a609ea634ec4a5ff846049b9dc12b40b5f1a702` |
| Incoming baseline, `AC-Integration` | `000c1bd9baded808b79a04b7f666cacabce64939` |
| Common ancestor | `66a529248d3198ed70dc5489d82868bc33a37796` |
| Integration source branch | `integration/ac-into-main` |
| Working branch after promotion | `main` |
| Exact promoted head | `e627a39e6c27cd4432ab063741fe726af8378a63` |

The integration commit retains both input commits as parents. The input branches
and their historical source/evidence identities are preserved.

## Frozen boundary and completed review

The first integration is pinned to the two revisions above. The merge commit is
`5a44e985c15a302110fd91d064431f1183e55857`, with both pinned commits retained as
parents. [PR #2](https://github.com/randogelist/Methboke/pull/2) merged this
history into main without a new merge commit; GitHub's recorded merge commit
is the promoted head `e627a39e`.

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

## Source acceptance and promoted head

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

The exact pre-promotion head `e627a39e6c27cd4432ab063741fe726af8378a63` passed
[run 44856391458](https://github.com/randogelist/Methboke/actions/runs/44856391458).
Independent review confirmed **654 reused modules, zero freshly compiled
modules, 169 fresh package audits and 2,212 named type/axiom reports plus
fresh QFB**. Dependency and project cache admission were both EXACT, only
`propext`, `Classical.choice` and `Quot.sound` occurred, and recovery was skipped.
The original `5a44e985` acceptance and this later exact head check remain
separate records.

The first main run, [44857663580](https://github.com/randogelist/Methboke/actions/runs/44857663580),
passed at the same promoted commit, including final acceptance and full cache
publication. It reused 548 modules and freshly compiled 106, with 169 fresh
package audits and 2,212 named reports plus QFB; dependency cache was EXACT,
project cache PREFIX, and recovery was skipped. Its donor was
`572fd9ee` / run `44848985720`. The downloaded evidence archive SHA256 is
`ffa9f5044ade02ddda080770ab165920fabf0a2ff70c6a2b7a814228fff41c49`.
A subsequent documentation commit still requires its own exact-head check.

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

Each new verification must pass all 654 registered build modules, 169 fresh package
audits, 2,212 exact named type/axiom reports, the fresh QFB cutout, evidence
retention, publication, and the final `Material accepted` gate. The incoming
and main theorem type/axiom maps are compared with the candidate's reports.
Only `propext`, `Classical.choice` and `Quot.sound` are permitted.

Missing or incompatible external dependency objects are an obstruction. They
do not authorize local Lean execution or compilation of Mathlib from source.
Previous accepted evidence and cache snapshots are retained on failure.

## Completed promotion and main verification

The full evidence must identify the actual tested source commit and run.
A documentation-only acceptance commit keeps that source identity in the
archive and receives its own ordinary external check. Its changes must preserve
all proof, audit, registration, pin, verifier and workflow inputs. The original
accepted-source archive remains authoritative for that run; a later green head
run is separate readiness evidence and does not require another documentation
commit merely to record another run.

The authorized promotion re-read main and the reviewed PR head, confirmed
main still matched the pinned baseline, and fast-forwarded main without force
to the verified `e627a39e` history. This preserves the original two-parent merge
and both inputs. GitHub confirms PR #2 closed and merged at 2026-11-21
02:46:09 UTC, with merge commit `e627a39e6c27cd4432ab063741fe726af8378a63`.

The current working-branch and completed-task selectors in GPT, README and
status records now identify main and `MERGED_COMPLETE`. The original receipt's
integration branch, tested commit and run remain immutable. These synchronization
edits remain documentation-only and follow the ordinary exact-head check rule.

The first ordinary main run established the combined cache in
main's own branch scope. GitHub's [cache access rules](https://docs.github.com/en/actions/reference/workflows-and-actions/dependency-caching)
allow the current/default branch, and main cannot restore a cache created only
on its child integration branch. The observed main run reused the compatible
548-module donor at `572fd9ee` and compiled 106 additions externally before
publishing the combined main snapshot. Preserve the existing single-donor
validation and publication rules; later reuse remains subject to those checks.

The promotion documentation commit uses an ordinary message so its main head
receives the existing external check after the first main cache is published.
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

[Detailed promotion review](reviews/PROMOTION_REVIEW.txt) preserves the historical
pre-promotion workflow, cache and history review. Later AC generator work remains a
separate, source-pinned follow-up under the same preservation and verification
requirements.
