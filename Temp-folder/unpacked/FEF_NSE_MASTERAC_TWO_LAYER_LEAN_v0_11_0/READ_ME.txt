MASTERAC TWO-LAYER RELEASE v0.11.0

PUBLIC LAYERS
- Layer A Mathematics: LayerA_Mathematics.lean
- Layer B Physics: LayerB_Physics.lean

Dependency direction: Layer B -> Layer A only.
See TWO_LAYER_RELEASE.txt and LAYER_MAP.tsv.

v0.7.7 -- EXPLICIT STORAGE REWRITE TARGETS

v0.7.6 user run: 18 modules compiled, through KernelCalculus.
KernelBirth, KernelCritical and KernelCalculus now pass.
KernelStorage failed at two rewrite/inference boundaries.

1. kernel_supplied_rate_nonpositive
The generic mulAdd rewrite expanded the lower side of the weighted inequality.
The transitivity step instead needs w*(g*x+c*d) expanded to w*(g*x)+w*(c*d).
The rewrite now names those arguments explicitly. The lower side remains
w*(xRate+action), exactly as required by the following ht-prime calculation.
2. kernel_paid_cells_telescope
The telescoping lemma now receives the explicit sequence
  fun k => s.actionPrimitive (s.grid k)
and the prefix length n, followed by the existing initial-value rewrites.

Only these two proof-body rewrite commands change.
All 323 theorem statements and hypotheses are unchanged.
All other 35 Lean files are byte-identical to v0.7.6.
All 18 passing modules from the v0.7.6 user run remain byte-identical.
The previously repaired field declarations are retained.
No new theorem, mathematical premise, dependency or resource limit is added.
The 149 reconstruction scripts are cumulative additions since checked v0.6.1;
this repair introduces zero additional theorem declarations.
Static source and preservation checks pass; native compilation remains pending.
The complete user-checked baseline remains v0.6.1 (174 theorem reports).

FEFFERMANN INTERNAL KERNEL RECONSTRUCTION -- v0.7.7

BASELINE: v0.6.1 passed on the user native Windows Lean 4.33.0 compiler.
24 modules; 174 theorem reports; no sorryAx; zero project research declarations.
Every checked declaration statement and proof body is retained.
THIS RELEASE: 36 modules; 323 theorem reports; 149 new theorem scripts.
NEW LEAN COMPILATION: PENDING USER COMPILER. Static checks are not a kernel check.

RECONSTRUCTED INTERNAL ROUTES
QUATROS: finite action square completion -> exclusive survival/ownership ->
causal path retention -> four-fifths capacity -> exact 509/605 renewal ->
supplied storage and bounded paid primitives -> M7 -> critical bounds -> Serrin.
reconstructed_quatros_port fills all five internal fields for explicit observables.
MAOTAOTROS: differential witnesses -> integrated source/critical balances ->
actual source cells -> canonical minimal paid defect -> local/global excess ->
signed production budget -> same-object critical control.
reconstructed_maotaotros_port fills its internal critical field.
Finite same-measure packet Young/absorption and integrated critical consequences
are derived from a modal energy identity and finite capacity allocation.
Covariance: strict-loss renewal + actual prefix realization -> uniform prefix.
This constructs a concrete prefix port separately for R3 and T3.
Existing finite spectral, reduced-capacity and T3 integral identities are retained.

PUBLIC ENTRY POINTS
Master_r3: MR3 retained; MR3_reconstructed adds the explicit internal instances.
Master_T3: MT3 retained; MT3_reconstructed adds the periodic covariance instance.
Feffermann-Classification imports both. The four requested details/derivation
files remain public; the derivation files import the new supporting modules.

WHAT IS STILL OPEN
Ordinary real/complex arithmetic and calculus instances; actual integrating
factor/time-grid realization; lower modal/packet and geometric-census ports;
projection optimality; T3 character integrals and unconditional Fourier
completion; same-physical-solution insertion and analytic continuation exits;
classification force instances and breakdown witnesses.
The MAOTAOTROS local excess and canonical paid-prefix bound remain source inputs.
The covariance source explicitly requires both physical realization and payment.
No equivalence of private QUATROS/MAOTAOTROS trajectories is invented.
NSE_CASE_PROVED=NONE. No percentage of the earlier project is claimed.

AUDIT AND SOURCE COVERAGE
RECONSTRUCTION_COVERAGE.tsv explains each selected source-to-Lean derivation.
ROCQ_FILE_INDEX.tsv / ROCQ_DECLARATION_INDEX.tsv inventory all five source archives;
inventory entries do not assert that every declaration has been ported.
FRONTIER.tsv separates physical inputs from existing Rocq proofs awaiting translation.
Types.lean prints the input records; Audit.lean requests every theorem dependency report.
SOURCE_AUDIT.json records static checks and explicitly lists checks not performed.

RUN
Use RUN_FROM_DOWNLOADS.txt / run.cmd. Native Lean 4.33.0, 16 threads, fresh build.
No network, Python, PowerShell, Lake, or dependency downloads in the runner.
The conditional kernel-elaborated markers are emitted only after compilation
and the full printed dependency-report check succeed.

v0.8.0 R3 intrinsic-identification addendum
------------------------------------------
A new module Fefferman/IntrinsicIdentification.lean freezes the exact logical
composition from Fefferman-admissible R3 force embedding plus an intrinsic
force global-closure theorem to A and exclusion of C.  The standard analytic
force embedding is documented in FEFFERMAN_R3_INTRINSIC_IDENTIFICATION.txt.
The hard R3 intrinsic global-closure theorem is NOT supplied and no Fefferman
case is claimed proved.

PHYSICS EXTENSION v0.10.0
This extension does not alter the compiled NSE/Fefferman theorem statements.
It adds a separate derivation layer for the MasterAC-as-framework presentation:
transport/dual pairing, first variation, Noether conservation, classical
Euler-Lagrange, GP-shift quantum CCR, state/observable picture duality, and the
Cartan curvature-action expansion.  The differential-geometric
stationary-action -> Einstein-equation step remains an explicit realization
port; QM <-> GR round-trip equivalence is not claimed.
