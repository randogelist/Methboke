# Weak_Fourierman_B repository workflow plan

Date: 2026-11-19. Repository: `randogelist/Methboke`, working branch `main`.
Inspected base: `43530b70d044624cbf83a3480840187a567549a5`.
State: **four modules activated; external compiler/audit acceptance pending**.
The historical stage plan below is retained; the activation record supersedes
its preparation-only status.

## Scope and notification rule

Methboke's fixed goal remains finite-cap analytic admission and the distinction
between admitted evolution and universal germ-to-cap extension. Weak_Fourierman_B
is the current supporting conditional regularity workstream. It uses smooth
periodic divergence-free mean-zero data, viscosity `nu > 0`, the full finite
squared Fourier budget on `(0,min(Tmax,Tf))`, and the same maximal trajectory.
`Tf = ||a||_2^4/(8*pi^2*nu^5)`. Neither universal budget finiteness nor universal
analytic admission is established by this criterion.

The user requested **chat-only `<->`** when any one of the ten contextual
obligations reaches A-tier, and again for the exact complete root. No scheduled
monitoring, polling task, webhook, or automatic chat notification is part of this
workflow. The previously created daily watch has been disabled.

At an active review after matching external evidence is available, announce
`<-> WFB-01 — local-front Fourier-to-Serrin` or the corresponding obligation.
Name its exact statement, scope and evidence. A leaf helper or infrastructure
pass does not complete a contextual obligation. Record that announcement only
after it is actually made. Never issue the root sign for a partial package pass.
The finite-budget premise remains in the exact root type; all auxiliary analytic
existence, continuation, identification and gluing obligations must be proved.

## Stage A: completed source preparation

This commit brings the current cumulative B-tier argument, indexed source map,
machine-readable ten-obligation register and four exact candidate modules into
the repository. It also synchronizes GPT, README, index and status metadata.

The owned sources are staged at
`candidate/src/MethbokeAddon/WeakFouriermanB/` under this directory, outside
`Material/`. `candidate-sources.json` binds their hashes, imports and all required
audit names. The staged dependency order is:

1. `PhysicalFourier`: 13 declarations; prior user-reported cached acceptance.
2. `FourierBudget`: 5 declarations; repaired source with prior user-reported
   cached acceptance. The stale failed v0.1 source is deliberately excluded.
3. `LocalFront`: 29 declarations; prepared repair, external acceptance pending.
4. `HomogeneousBudget`: 10 declarations; prepared, external acceptance pending.

There are **57 declaration audit requirements and 1,255 source lines**, not 57
completed contextual obligations. No compiled objects or Windows/WSL checkpoint
receipts are imported into GitHub Actions. There is no new repository compiler
pass for these files.

The original local Docker workflow remains an external replay option. Its
Simon/test paths, container locks and payload-pointer scripts are not ported as
the repository build driver. No active Lean source, pinned vendor source,
dependency lock, Lake configuration, build driver or workflow is changed by
this preparation stage.

This preparation-only commit uses `[skip ci]`: current `material.yml` runs on
every push to main, so otherwise even this plan could launch verification and
full recovery. This is an explicit skipped verification, never a green result.
The subsequent active implementation/verification commit must not use that
marker. See [GitHub's documented behavior](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/skip-workflow-runs).

## Inspected infrastructure and migration hazards

The package has 269 vendored modules and 14 endpoint wrappers: 283 own modules,
14 endpoint audit packages, 41 declaration audit entries and the separate QFB
cutout. Preserve all of them and their evidence. The compiler remains
`leanprover/lean4:v4.33.0`; Mathlib remains
`db584cd6d46c92f209a44c0f1c829460d327499d`.

The retained source-specific verified baseline is recorded in INDEX-WORTHY.
Additionally, read-only inspection found successful workflow runs
[44101003716](https://github.com/randogelist/Methboke/actions/runs/44101003716)
and [44126844972](https://github.com/randogelist/Methboke/actions/runs/44126844972)
at the inspected main SHA. For the latter, the fast job and final acceptance
job succeeded and recovery was skipped; evidence and binary artifacts remain
available. This round inspected job/artifact metadata, not the full theorem
audit contents. It therefore does not replace the accepted theorem-evidence
ledger or certify WFB. Inspect the matching receipts before selecting a restored
baseline for the new verification run.

Three implementation constraints must be resolved before activation:

| Constraint | Observed source | Required treatment |
|---|---|---|
| Package changes can invalidate the whole baseline | `native_registry.py` cache keys include `lakefile.lean`; native receipt context includes plan configuration hashes | Do not add a `lean_lib` and assume warm reuse. Demonstrate compatible receipt restoration first. |
| Recovery currently follows any unsuccessful fast worker | `material.yml` recovery condition checks `accepted != true` | Distinguish missing/corrupt cache infrastructure from theorem, audit, static-validation and publication failures. |
| Owned additions differ from the pinned upstream closure | `build.py` discovers native modules; export/provenance tooling assumes vendor records for source-graph members | Add an explicit owned-source provenance model without rewriting the vendor manifest or pretending WFB came from Methlib. |

## Stage B: prepare cache-safe activation and failure routing

1. Capture a source-only plan for the existing baseline and intended WFB
   additions. Inspect the current report, compiler/lock/policy identity and
   per-module receipts. Do not run Lean locally or execute a wrapper to obtain it.
2. Use the native direct compiler's discovered module paths if compatible:
   intended active source path is
   `Material/MethbokeAddon/WeakFouriermanB/*.lean`. It may permit registration
   without changing the Lake file. Confirm generated search paths, module-index
   discovery, recursive dependency closure, export handling and receipt context
   against actual source before choosing this route. It is not yet certified.
3. Add four explicit wrapper/audit packages for the four source modules. Keep
   all 57 exact declaration checks and the existing 41 checks plus QFB cutout.
   An unchanged `.olean` does not replay embedded `#print axioms`; generate/run
   dedicated fresh audit inputs for every required endpoint on verification.
4. Register owned source provenance separately from `_vendor/source-manifest.json`.
   Preserve module names, exact initial proof bytes and dependency pins. Bind the
   future active paths and audit files to source hashes and exact intended types.
5. Resolve cache-key/receipt compatibility explicitly. If active registration
   can retain all semantic compile-context hashes, reuse unchanged baseline
   objects through the existing receipt checks. If a necessary driver or Lake
   change invalidates context, do not weaken or silently bypass validation:
   implement and review a versioned compatibility adapter, or report the cache
   obstruction before attempting a rebuild. A new audit policy must still bind
   fresh audit evidence even where compiled-object reuse is justified.
6. Introduce explicit fast-worker failure classes. Cache missing/corrupt or
   incompatible-object failures may select existing bounded recovery when its
   requirements are satisfied. A new Lean proof/type/axiom failure must fail the
   candidate, preserve accepted objects, and expose the first relevant log;
   rebuilding all 283 foundations is not its remedy. Static source errors,
   publication errors, cancellation and unknown failures must not silently
   become cold compiler runs. Publication retry may reuse already verified
   outputs only after their exact identities and receipts are checked.
7. Keep dependency restoration separate: no Mathlib source rebuild on a cache
   miss, no cache deletion and no compiler/lock upgrade. A failed candidate
   cannot replace a passed baseline or publish a passed whole-project cache.
8. Check source discovery, owned/vendor provenance, audit coverage, stale
   receipt rejection and failure routing using nonexecuting static inspection
   here. Meaningful executable control tests and Lean verification belong to
   the authorized external runner, consistent with the repository rules.

Do not promise that adding a new namespace is cache-neutral: the migration gate
must demonstrate which of the 283 receipts remain valid. Keep `MATERIAL_JOBS=2`
and `LEAN_NUM_THREADS=2` initially; they are separate controls. Optimize only
after comparable timings identify a dominant phase.

## Stage C: external cached verification and chat handoff

Activate the first dependency-closed source layer only after Stage B is ready.
Prefer PhysicalFourier -> repaired FourierBudget -> repaired LocalFront first;
activate HomogeneousBudget after that layer is accepted if the driver is
package-all-or-nothing. All four may be included in one attempt only if failed
dependencies are handled explicitly and no partial failure can be published as
a complete accepted package. Never reduce the required audit scope for speed.

Use the established cached external Material workflow; retain its registry
backend as an alternative only with matching identity checks. This does not
claim native Windows acceptance. A later Windows `run.cmd` must use a matching
Windows toolchain/cache and a supported registration path; the existing WSL
Docker script is a different environment. Native direct compiler activation
does not automatically make Lake target names or standalone exports work.

On each verification record:

- source commit, module/source/audit hashes, exact compiler and dependency lock;
- runner OS/architecture, baseline receipt identity and cache class;
- dependency restore, own compilation, fresh audit, diagnostics/export and job
  wall time separately; per-module reused/fresh/failed status;
- module-worker count and Lean-thread count;
- required exact types, complete fresh axiom outputs and source preservation;
- publication outcome separately from the theorem verification outcome.

The 2026-11-19 sustained-work instruction permits continued independent source
preparation while an external runner verifies the committed layer. Inspect
available results and repair or advance without requiring another `go on`.
Preserve the tested commit and avoid superseding it with unrelated pushes.
No scheduled monitoring is introduced. Emit the chat-only sign only after
accepting the evidence for an entire
contextual obligation. Update `obligations.json`, GPT and relevant indices with
the exact acceptance and announcement scope; do not infer root acceptance from
the first two obligations.

## Stage D: build the remaining mathematical obligations

The dependency-oriented sequence after the prepared bridges is:

- WFB-03 physical periodic H1 local existence with norm-controlled lifespan;
- WFB-04 finite-front strong uniqueness and normalized pressure;
- WFB-05 same-path maximal trajectory and extended lifetime;
- WFB-06 actual enstrophy inequality and same-path endpoint continuation;
- WFB-07 strict `Tf < Tmax`, including equality and infinite-lifetime cases;
- WFB-08 smooth-data admission and localized weak-strong identification;
- WFB-09 same-path QFB tail, pointwise pressure agreement and smooth gluing;
- WFB-10 exact root, zero datum, all lifetime cases and final audit.

Independent mathematical work may be prepared in parallel, but a declaration
is accepted only after its dependency-closed external evidence passes. The
published local H1 theorem used in B-tier prose still needs a genuine Lean
development or an existing correctly typed formal theorem. Scalar Gronwall,
fixed-cutoff Galerkin existence, or a record containing the desired continuation
implication does not discharge the physical local theory.

## Exit condition of this planning change

The repository contains the exact candidate sources and a reviewable migration
plan with ten individually tracked obligations. Active Material build behavior
and all established source/cache identities are preserved. No new obligation is
marked A-tier, no external run is claimed, and no success sign has been issued.

## Activation record — 2026-11-19

Stage B and active registration are prepared: four source modules copied with
matching staged SHA256; four wrapper/audit packages; 57 unique declaration audit
pairs with explicit principal type assertions. Full scope is 291 modules,
18 packages, 98 declaration audits and the unchanged QFB cutout. Separate owned
provenance validates source bytes/imports and standalone exports. Lake, lock,
compiler and vendor source manifest remain unchanged.

The receipt adapter recognizes only the exact reviewed legacy driver/configuration
context, reconstructs source/import receipt identities, and validates every
restored object before rebinding. All 283 prior identity calculations match by
static reconstruction; object-byte validation belongs to the external run.
Typed current cache rejection alone can trigger automatic recovery. All other
failures remain failures; candidate outputs cannot replace a passed baseline.

The retained run 44126844972 report and 15 fresh audit-log hashes were reviewed;
see ../../audits/material-43530b7/summary.json. This verifies only the baseline.
New source, audit, receipt and routing controls await external execution.

WFB-03 is blocked at genuine cutoff-uniform physical local H1 construction.
The seven-declaration SmoothDatum source in next/ is an independent WFB-08 input
helper, prepared only. No downstream root assembly bypasses the missing edge.

## First acceptance and next registered layer

Run44537934256 at0402aa37 accepted the four initial modules, all98 declaration
audits and cutout with only standard axioms. All283 baseline objects were
reused and eight additions built; 183 controls passed. WFB-01/WFB-02 are
accepted with exact evidence in ../../audits/material-0402aa37/summary.json.

The next registered layer has six modules and22 additional declarations:
SmoothDatum, FiniteFrontTest, FiniteWindowCrossIdentity,
FiniteWindowRelativeEnergy, FiniteWindowSerrinComparison,
LocalFrontIdentification. Full scope303 modules/24 packages/120 declarations
plus cutout. It prepares genuine same-path finite-front identification without
assuming a global classical NSE solution. No CI driver or dependency pins change.
Physical local H1 existence and the full root remain unresolved; later
compact-cylinder and gluing candidates are excluded from this run.

## R0 final source layer

The second layer passed at67f7663/run44540921991 with all120 fresh audits and
291 reused/12 freshly built modules. The third registered layer contains seven
R0 packages and34 declarations, including exact classical and analytic finitecap
admission roots. Scope317 modules/31 packages/154 audits plus cutout. Actualcap
admission remains explicit; WFB-03 and R1 are not discharged. All initial
compiler/dependency/Lake/CI identities and passed source bytes are preserved.

The first R0 run0ddd2d67 failed before audits on two syntactic rewrites.
Corrections and the literal D_Q data-class adapter are prepared for321 modules,
33 packages and161 declarations pluscutout. The303-module accepted baseline
remains intact; no recovery/full rebuild was selected by the proof failure.
