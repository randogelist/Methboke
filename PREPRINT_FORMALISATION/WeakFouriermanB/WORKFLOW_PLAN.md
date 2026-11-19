# Weak_Fourierman_B repository workflow plan

Date: 2026-11-19. Repository: `randogelist/Methboke`, working branch `main`.
Historical inspected base: `43530b70d044624cbf83a3480840187a567549a5`.
Current state: **exact R0 finite-cap admission accepted at `93ca8a5`; WFB-01
and WFB-02 accepted; eight WFB obligations, the exact WFB root and R1 open**.

[Run 44549257770](https://github.com/randogelist/Methboke/actions/runs/44549257770)
verified 321 modules (303 reused, 18 freshly compiled), all 33 fresh endpoint
packages and 161 declaration audits plus the QFB cutout. All 183 controls passed;
all theorem audits use approved standard axioms only. The
[matching evidence](../../audits/material-93ca8a5/summary.json) accepts the
literal `D_Q_subset_R_nu` and classical/two-sided analytic finite-cap roots,
including preservation of velocity and normalized pressure on `[0,T)`.
Actual cap admission remains explicit; universal germ extension is not proved.

The stage A–C plan and initial activation record below are historical snapshots
of preparation and migration requirements, not current pending-acceptance claims.
The final acceptance record identifies their completed external verification.
Stage D continues to track the remaining WFB work.

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

## Historical Stage A: source preparation

That preparation commit brought the then-current cumulative B-tier argument, indexed source map,
machine-readable ten-obligation register and four exact candidate modules into
the repository. It also synchronized GPT, README, index and status metadata.

The initial owned sources were staged at
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
receipts are imported into GitHub Actions. At that preparation stage there was no repository compiler
pass for these files; subsequent acceptance is recorded below.

The original local Docker workflow remains an external replay option. Its
Simon/test paths, container locks and payload-pointer scripts are not ported as
the repository build driver. No active Lean source, pinned vendor source,
dependency lock, Lake configuration, build driver or workflow is changed by
this preparation stage.

That preparation-only commit used `[skip ci]`: the then-current `material.yml`
ran on every push to main, so the plan alone could have launched verification
and full recovery. This was an explicit skipped verification, never a green result.
The subsequent active implementation/verification commit must not use that
marker. See [GitHub's documented behavior](https://docs.github.com/en/actions/how-tos/manage-workflow-runs/skip-workflow-runs).

## Historical inspected infrastructure and migration hazards

The inspected baseline had 269 vendored modules and 14 endpoint wrappers: 283 own modules,
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

The following three constraints had to be resolved before activation:

| Constraint | Observed source | Required treatment |
|---|---|---|
| Package changes can invalidate the whole baseline | `native_registry.py` cache keys include `lakefile.lean`; native receipt context includes plan configuration hashes | Do not add a `lean_lib` and assume warm reuse. Demonstrate compatible receipt restoration first. |
| At the inspected base, recovery followed any unsuccessful fast worker | `material.yml` recovery condition checks `accepted != true` | Distinguish missing/corrupt cache infrastructure from theorem, audit, static-validation and publication failures. |
| Owned additions differ from the pinned upstream closure | `build.py` discovers native modules; export/provenance tooling assumes vendor records for source-graph members | Add an explicit owned-source provenance model without rewriting the vendor manifest or pretending WFB came from Methlib. |

## Historical Stage B: cache-safe activation and failure routing

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

## Stage C: external cached verification and chat handoff contract

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

The remaining dependency-oriented WFB sequence after the accepted bridges is:

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

## Historical exit condition of the planning change

At the planning-only snapshot, the repository contained exact candidate sources
and a reviewable migration plan with ten individually tracked obligations. Active
Material behavior and source/cache identities were preserved. That snapshot
claimed no new A-tier obligation or external run and issued no success sign.

## Historical initial activation record — 2026-11-19

Stage B and active registration were prepared: four source modules copied with
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
At that snapshot the new source, audit, receipt and routing controls awaited
external execution; the following records supply the subsequent results.

WFB-03 is blocked at genuine cutoff-uniform physical local H1 construction.
The seven-declaration SmoothDatum source was an independent prepared WFB-08
input helper, subsequently accepted at `67f7663`. It did not discharge WFB-03.
The R0 path uses an actual admitted front and does not bypass or prove that edge.

## Accepted source layers

Run `44537934256` at `0402aa37` accepted the four initial modules, all 98
declaration audits and cutout with only standard axioms. All 283 baseline
objects were reused and eight additions built; 183 controls passed. WFB-01
and WFB-02 have exact evidence in
[the first-layer summary](../../audits/material-0402aa37/summary.json).

Run `44540921991` at `67f7663` accepted six further modules and 22 additional
declarations: SmoothDatum, FiniteFrontTest, FiniteWindowCrossIdentity,
FiniteWindowRelativeEnergy, FiniteWindowSerrinComparison and
LocalFrontIdentification. Its scope was 303 modules, 24 packages and 120
declarations plus cutout, with 291 objects reused and 12 freshly built. This
established same-path finite-front identification without assuming a global
classical NSE solution. See the
[second-layer summary](../../audits/material-67f7663/summary.json).

The R0 layer initially registered seven packages and 34 declarations at scope
317/31/154. Two-sided analytic-cap and exact data-class adapters later added
two packages and seven declarations, giving 321/33/161. These nine R0 packages
and all preceding packages are accepted at `93ca8a5` / run `44549257770`, with
all required audits fresh and successful receipt-checked publication. The
literal `D_Q_subset_R_nu` includes the zero solution and actual nonzero cap.
Classical and two-sided analytic roots preserve velocity and normalized
pressure. Compiler/dependency/Lake identities and the pinned vendor sources
remain unchanged. This result does not discharge universal R1 or any further
whole WFB obligation.

## Historical R0 verification feedback

The first R0 run at `0ddd2d67` failed before audits on two rewrite matches.
Proof corrections preserved statements. The `c6e039da` recheck compiled those
gluing/pressure corrections but stopped in initial-trace filter notation and
composition normalization. Typed eventual bounds and explicit composition
expansion repaired those sites without changing statements or the final scope.

Run `44547124107` at `d2c0259` compiled all 321 modules and passed 19 audit
packages, including the literal R0 root. Its required pressure audit stopped
at an unused namespace absent from the imports. A one-line setup correction
preserved every proof, signature assertion and axiom audit. Each failed run
preserved the accepted 303-module baseline and skipped recovery. They supplied
no aggregate acceptance; the subsequent full pass at `93ca8a5` is the current
acceptance record, with 303 reused and 18 freshly compiled modules.

## Current B-tier source index (2026-11-19)

The [remaining route](../../WFB_ROUTE_ANCHOR_INDEX_B_TIER.txt) and
[126-anchor register](ANCHOR_INDEX_v0_2.json) map ten work packages R01–R10 to
the existing contextual obligations. The first formal edge remains R01/WFB-03:
cutoff-independent physical H1 local existence. Later entries are prospective;
accepted R0 comparison, pressure and gluing layers are explicitly reused.
This documentation-only round changes no proof, audit, CI or acceptance status.

## WFB main-goal implementation authorized


WFB_LOCAL_THEORY_LAYER_1_PREPARED_2026_11_19
The user explicitly identifies WFB as the main goal and authorizes sustained
implementation, largest open gap first, with independent work between commits
and external runs. This supersedes the former supporting-workstream role.
The exact WFB conclusion retains the finite full Fourier-square budget; no
universal budget bound or universal analytic germ-extension claim is added.
Accepted R0 remains a reusable foundation, not the current main target.

Seven new owned modules provide40 public theorem candidates: a scalar cubic
short-time barrier; cutoff-uniform actual Galerkin H1/H2 estimates; local
all-order/RHS/time-modulus bounds; genuine finite-window compactness; actual
local classical velocity/pressure uniqueness including0; physical time
translation; arbitrary-field Hessian/nonlinear/absorption estimates.
The square budget in the local Galerkin construction is derived, not assumed.
The explicit lifespan is1/(16*(C/nu^3+1)*(R+1)^2), withR an upper bound for
initial physicalDissipation. It is independent of cutoff and higher norms.
The final physical solution construction still needs its limit/recovery layer.

Prepared external scope:335 compiled modules (269 vendor+26owned+40wrappers),
40 fresh endpoint packages,201 declaration type/axiom audits plusQFBcutout.
All321 accepted module inputs are unchanged and eligible forcompatible reuse.
All previously required audits rerun freshly. Compiler,dependencylock,Lake,
CI drivers,cachecompatibility policy andvendor bytes remain unchanged.
No local Lean,Lake,kernel audit orproject tests. No new acceptance signal.
OnlyWFB-01/02 currentlywhole-obligation accepted;WFB04uniqueness is a candidate
pendingmatchingexternalverification. The completeWFBroot remains unverified.
Nextindependentpreparation: finite-windowSobolevlimit/physicalrecovery and
uniformphysicalexistence, maximaltrajectory, finite restartgluing, physical
enstrophytimeidentity, budgettouniformH1, strictcutoff andR0rootassembly.

Full source chain and first compiler feedback

WFB_FULL_CHAIN_PREPARED_2026_11_19
The largest gap now has a complete source candidate: a cubic barrier gives
cutoff-uniform local Galerkin bounds, all-order compactness yields an actual
Sobolev flow, and physical recovery constructs a normalized classical NSE front
with duration controlled only by viscosity and the physical H1 bound. The
local square budget is derived; no AX6 or local-existence premise is retained.

Actual-front uniqueness fixes one maximal velocity/pressure pair. Finite
restart gluing gives uniform-H1 continuation. The physical enstrophy derivative
and arbitrary-field nonlinear estimate yield a common H1 bound from the whole
open-interval integral of actual dissipation squared. A literal physical-budget
extension theorem preserves the entire original velocity and pressure.

The Fourier budget up to min(Tmax,cutoff) supplies that integral. If Tmax is at
most the cutoff, including equality, continuation contradicts finite maximality.
Thus cutoff<Tmax. Accepted classical R0 then yields one global smooth pair
preserving the whole maximal trajectory, and maximality gives Tmax=infinity.
The exact root is MethbokeAddon.WeakFouriermanB.Weak_Fourierman_B.
Separate contextual adapters retain one original Leray-Hopf witness through
all pre-endpoint intervals, Q09, normalized tail overlap and global gluing.

22 new owned modules / 104 public theorem candidates since accepted R0 are now
registered: 365 compiled modules = 269 vendor + 41 owned + 55 wrappers;
55 fresh endpoint packages / 265 declaration audits plus fresh QFB cutout.
All 321 accepted module sources remain unchanged. Compiler, Mathlib, vendor,
Lake, dependency lock, CI and cache drivers remain unchanged. No local Lean.

First external attempt 4bd466f1 / run44560978167 failed at three proof
expressions: addition order, explicit Ici positivity, and scalar zero after
vector extensionality. All three repairs preserve statements. Native cached
verification reached those failures after container OOM fallback; required
audits were not reached. Evidence: audits/material-4bd466f1-failed/summary.json.
The complete prepared chain requires matching external compiler/type/axiom
verification. Only WFB-01/02 are currently whole-obligation accepted. No new
acceptance sign, universal budget bound or universal analytic extension follows.
