# QFA: accepted foundations, restart, free-heat generator and zero datum

**Status: A-tier accepted for the exact foundation, restart, heat-smoothing,
free-heat time-energy and generator, all-window weighted-budget and zero-datum scopes below.**
The complete physical QFA and WFA theorems remain formally open in this project.

The [NSE-A finite-charge regularity class](../A-Regularity-class/README.md)
separately registers the B-tier six-charge characterization and datumwise
global-regularity equivalence from the written WFA chain. That registration
adds no theorem to the accepted native scope described here.

## Current construction: forced L2 response and physical energy pairing

**Matching external verification is pending** for three new packages:

| Package | Prepared scope |
|---|---|
| `QFAHeatDuhamel` | Actual retarded integral, continuous zero trace, forcing-class invariance and exact time-L2 forcing bounds; 15 declarations |
| `QFAHeatDuhamelOperator` | Actual bounded map from the forcing Lp quotient to continuous L2 paths, norm at most sqrt(T), zero trace and representative compatibility; five declarations |
| `QFAHeatSpatialEnergy` | Actual H1 integration by parts, H1-H2 Laplacian pairing, bilinear H2 symmetry and negative-enstrophy identity; four theorems |

The batch has **24 declarations: 22 theorems and two definitions**, covered by
29 independent consumers. The expected complete run is **534 modules,
109 fresh package audits and 1,435 named reports**. Prepared source is not
A-tier acceptance. The generator acceptance below and all earlier scopes remain.

The response uses finite-window time-L2 spatial-L2 forcing. Forced maximal
regularity, the inhomogeneous derivative equation and nonlinear local theory
remain separate obligations. Steps 1 and 7 remain complete; step 3 is open.

## Accepted actual free-heat generator and equation from the initial trace

**Nine theorems are A-tier accepted at `809aadc6`**, with eleven
independent consumers, in [external run 44853804320](https://github.com/randogelist/Methboke/actions/runs/44853804320).
The complete run passed **528 modules, 106 fresh package audits and 1,411 unique
named type/axiom reports**, plus fresh QFB, complete publication and the final gate.
[Independent review](../../audits/material-809aadc6-qfa-heat-generator-accepted/independent-review.json) ·
[All nine theorem reports](../../audits/material-809aadc6-qfa-heat-generator-accepted/new-declaration-index.json) ·
[Exact derivation](DERIVATIONS/HEAT_GENERATOR_CHAIN.txt).

For arbitrary actual physical H1 data and positive viscosity, `QFAHeatGenerator`
proves the strong L2 time derivative of the actual free-heat velocity at every
positive time. Its derivative is exactly viscosity times the physical Laplacian.
That derivative belongs to finite-window L2 in time and is Bochner integrable
down to zero. The integrated equation starts from the **original continuous
H1/L2 initial trace**. Its exact derivative-energy coefficient is **viscosity
divided by two**. No derivative or integrability witness is supplied as a premise.

The H2 trajectory's auxiliary value at zero is used only in integrals; it does
not replace the true initial velocity or assert an H2 initial trace.
**Step 3 remains open. Steps 1 and 7 remain the only completed checklist items.**
The next microscopic target is the actual L2 Duhamel response for finite-window
time-L2 spatial-L2 forcing: continuity, zero initial trace and the sqrt(T) bound
using the actual forcing Lp norm, together with the integral-of-norm bound.
Forced maximal regularity and nonlinear H1 theory follow as separate obligations.

The accepted 35-declaration heat-time layer and the conditional main-branch
FDSN_R3 receipt below are retained. General QFA/WFA, five G-parent gaps, M2/M3
and the D-family root remain open; P01-P08/M1 and the Fefferman D goal are unchanged.
No local Lean was executed.

## Accepted free-heat time-energy and all-window weighted budget

**35 declarations are A-tier accepted at `000c1bd9`: 32 theorems and three
definitions**, in [external run 44851575278](https://github.com/randogelist/Methboke/actions/runs/44851575278). The complete run
passed **526 modules, 105 fresh package audits and 1,402 unique named type/axiom
reports**, plus fresh standalone QFB, complete publication and the final gate.
The matching [independent review](../../audits/material-000c1bd9-qfa-heat-time-accepted/independent-review.json)
checks the exact source, full types and standard-only transitive axioms.

| Package | Accepted scope |
|---|---|
| `QFAHeatTrajectory` | 15 declarations: the actual positive-time H2 heat trajectory, physical semigroup agreement, H2 continuity away from zero and strong time measurability |
| `QFAHeatTimeEnergy` | 19 declarations: exact enstrophy dissipation, actual Laplacian square integrability and finite-window L2-time H2 membership with a quantitative bound |
| `QFAWeightedBudgetAllWindows` | One theorem: actual LH product integrability and the factor-one-quarter weighted bound for every finite T >= 0, including the empty zero window |

**Checklist step 7 is complete for every supplied actual LH path.** Steps 1
and 7 are complete. Step 3 now also has the accepted actual free-heat generator
and integrated equation described above; the forced response, maximal regularity
and nonlinear H1 theory remain open. General-data global LH existence is a
separate step-4 obligation.
The H2 trajectory's zero extension at nonpositive times makes no H2 initial
trace claim for arbitrary H1 data; the physical H1 heat flow retains its original trace.

[Exact construction chain](DERIVATIONS/HEAT_TIME_ENERGY_CHAIN.txt) ·
[All 35 named declarations](../../audits/material-000c1bd9-qfa-heat-time-accepted/new-declaration-index.json).
Earlier failed attempts remain in the retained evidence and history registers.
The general QFA/WFA roots, five open NSE-A G-parent targets, P/M status and
Fefferman D project goal are unchanged. No local Lean was executed.

### Separate accepted main-branch FDSN_R3 result

Main source `572fd9ee`, [run 44848985720](https://github.com/randogelist/Methboke/actions/runs/44848985720),
has all **16 FDSN_R3 endpoints** accepted, including the original conditional
`Seed → Family` root. Its [retained independent evidence](../../audits/material-572fd9ee-fdsn-r3-accepted/independent-review.json)
records 548 modules, 137 fresh package audits and 1,320 named reports; the
FDSN_R3 scope comprises 493 declarations in 26 packages. This is explicitly
**main-branch provenance**. Seed existence, general QFA/WFA and the D-family
root remain open. Retaining this evidence neither imports FDSN_R3 into
AC-Integration nor changes the main branch or its proof scope.

## Earlier accepted restart, smoothing and zero-datum scopes

**Three native QFA layers are A-tier accepted at `ffbab0f5`**,
[external run 44847013775](https://github.com/randogelist/Methboke/actions/runs/44847013775). The complete run passed **520 modules,
102 fresh package audits and 1,367 named type/axiom reports**, plus standalone
QFB, publication and final acceptance. The new packages add **73 declarations:
53 theorems and 20 definitions/structures**. Only the approved standard axioms occur.

| Package | Accepted scope |
|---|---|
| `QFALHRestart` | Full physical restart of the same supplied LH path from its exact nonnegative energy-start trace, including translated momentum and all energy-class fields |
| `QFAHeatSmoothing` | Constructed actual positive-time H1-to-H2 heat map, native weak Hessians and quantitative Laplacian/H2 estimates |
| `QFAZeroDatum` | Exact physical root contract and complete zero-datum strict/closed QFA conclusion, including weak existence, every-path smooth tails, original-gradient energy equality and all future velocities |

**The general nonzero-data QFA theorem remains open.** Its cutoff is unchanged:
$8\|a\|_2^4/(27\pi^4\nu^5)$. Smooth pressure uses the explicit point gauge
$p(t,0)=0$. The new zero-datum result includes the closed cutoff at time zero.

[Exact acceptance](../../audits/material-ffbab0f5-qfa-accepted/independent-review.json) ·
[Full new-name register](QFA_CLOSURE_A_TIER_PROGRESS.txt) ·
[Scoped mathematical chain](DERIVATIONS/RESTART_HEAT_ZERO_CHAIN.txt).
No local Lean was executed. The project goal remains Fefferman D.

The next scoped construction is the **actual L2 Duhamel response** for
finite-window time-L2 spatial-L2 forcing: continuity, its zero initial trace,
the sqrt(T) bound using the actual time-L2 forcing norm and the integral-of-norm
bound. Forced maximal regularity, nonlinear H1 existence, general
LH existence, physical comparison, sharp spatial admission and small-product
continuation remain explicit general-data obligations.

## Earlier accepted foundation layers

The foundation batch was tested at `afd67db40e71bd1412c82247a78598288deb611e`
on `AC-Integration`. [External run 44788963412](https://github.com/randogelist/Methboke/actions/runs/44788963412)
passed compilation, fresh signature/type/axiom audits, publication and final
acceptance. The [receipt](../../audits/material-afd67db4-qfa-accepted/summary.json),
[independent review](../../audits/material-afd67db4-qfa-accepted/independent-review.json)
and [complete declaration evidence](../../audits/material-afd67db4-qfa-accepted/new-declaration-evidence.json)
retain that original scope. Later batches extend it as described above.

| Layer | Source | Scope |
|---|---|---|
| Physical contracts | `Material/MethbokeAddon/QuasiFeffermanA/Contracts.lean` | Actual full-volume L2, compact-test weak derivatives, solenoidal momentum tests and standard LH fields; no existence or regularity conclusion is inserted |
| Energy and traces | `Energy.lean` | Weighted product budget, strong initial/right traces, energy restart data and zero-datum velocity rigidity for supplied paths |
| Scalar cutoff | `Cutoff.lean` | Positive scalar threshold, exact half-budget identity, good-time selection and half-measure bound |
| Physical energy-class selection | `Integration.lean` | A genuine solenoidal weak-gradient energy trace strictly before the scalar cutoff; full shifted weak-PDE membership remains separate |
| Fourier multipliers | `FourierMultipliers.lean` | Five owned derivative-witness proofs; the exact original failed upstream port is retained inactive |
| Spectral realization | `Spectral.lean` | Derivative witnesses imply Fourier norm identities and the native spectral endpoint, without assumed norm identities or spectral realization |

The original native foundation has **35 accepted public helper theorems and
19 checked contracts/definitions**. Its four packages supply 188 named reports:
108 recovered QFA declarations, 14 representation declarations, 12 historical
conditional-root declarations, and 54 native declarations. All 698 names across
77 packages were freshly audited; all 463 required modules passed, with 420
prior modules reused and 43 compiled. There are 58 independent new consumers
(55 native and three historical-root consumers). Only the standard axioms
`propext`, `Classical.choice` and `Quot.sound` occur. No local Lean was executed.

## Exact finite-window result

For a supplied `LerayHopf nu a u G` path, put

$$E(t)=\|u(t)\|_2^2,\qquad Y(t)=\sum_{j=1}^3\|G_j(t)\|_2^2,\qquad M=\|a\|_2.$$

For every finite $R\ge0$, the product is integrable and

$$\int_0^R E(t)Y(t)\,dt\le\frac{M^4}{4\nu}.$$

For arbitrary $S>0$ and $\nu>0$, define

$$\theta=\frac{\nu^4}{S^6},\qquad
\tau=\frac{S^6M^4}{2\nu^5}.$$

Then $M^4/(4\nu)=\theta\tau/2$. If $a\ne0$, at least half the window
consists of genuine energy/weak-gradient good traces with $E(s)Y(s)<\theta$.
In particular there is $0<s<\tau$ with solenoidality, all three weak-gradient
witnesses, the energy inequality from $s$ to every later endpoint, translated
energy/trace data and strong right convergence to $u(s)$.

This is a pathwise selection theorem. It assumes a supplied LH path and does
not construct one. Its energy inequalities are standard defining LH assumptions,
not conclusions derived from the weak momentum equation alone. The original
`GoodRestart` record contains energy/trace data. The accepted `LHRestart.lean`
extension now proves the translated weak momentum equation and full shifted
LH membership at each nonnegative energy start, including the selected traces.

The explicit premise $S^6=16/(27\pi^4)$ gives the algebraic rewrite
$\tau=8M^4/(27\pi^4\nu^5)$. Admissibility of this Sobolev constant and the
physical continuation threshold remain unproved here. For zero datum the cutoff
is zero and every supplied LH velocity vanishes at every nonnegative time.
The accepted `ZeroDatum.lean` extension additionally constructs an actual zero
LH solution and proves the complete smooth-pressure, energy and future conclusion.

## Spectral scope

The spectral inputs are L2 fields with first-derivative and L2 Laplacian
identities against Schwartz test functions. The velocity itself need not be
Schwartz. The proofs derive the almost-everywhere Fourier multipliers, both norm
densities, weighted integrability and Plancherel energy identities, thereby
inhabiting `WholeSpaceSpectralEndpoint`.

Native LH traces supply first weak derivatives almost everywhere; the current
bridge does not manufacture an L2 Laplacian for every such trace. Actual physical
H1/H2 graphs and the Hessian–Laplacian identity were accepted in the subsequent
NSE-A batches. Positive-time heat H1-to-H2 smoothing is now accepted as well;
the sharp Sobolev/interpolation admission remains open.

## Ten-step construction status

| Step | Accepted scope | Remaining construction |
|---|---|---|
| 1. Concrete contract | Full-volume L2/LH interface and exact current physical root, with actual smooth pressure and strict/closed cutoffs separately checked | Contract complete; proving the general root belongs to steps 2–10 |
| 2. Spatial analysis | Actual H1/H2 graphs, Hessian–Laplacian identity, Fourier derivatives and real Leray projection | Sobolev/interpolation admissibility and the exact sharp constant |
| 3. Local H1 theory | Actual heat semigroup, H1-to-H2 map, measurable H2 trajectory, exact dissipation, finite-window L2-time H2, strong L2 generator and integrated equation from the original trace; zero nonlinear solution | Actual L2 Duhamel response, forced maximal regularity, arbitrary-H1 nonlinear existence, uniqueness and continuation |
| 4. LH solutions and restarts | Full shifted physical LH membership at nonnegative energy starts; actual zero-datum nonemptiness | General-data global nonemptiness |
| 5. Weak-strong uniqueness | Recovered abstract comparison statements retain their premises | Actual R3 relative-energy inequality and comparison |
| 6. Small-product continuation | Scalar threshold arithmetic | Physical evolution estimates, invariant bootstrap and global continuation |
| 7. Weighted budget | Complete: actual product integrability and one-quarter weighted bound for every finite T >= 0 of a supplied LH path, including T = 0 | No remaining step-7 packaging gap; general-data global LH existence belongs to step 4 |
| 8. Finite-window selection | Half-window measure, strict interior good trace, strong right trace and full PDE restart | Admissible sharp physical threshold and nonzero continuation |
| 9. Closed smooth tail | Complete zero-data smooth normalized tail and original-gradient energy equality at every nonnegative start | Nonzero-data smooth representative, pressure and energy equality |
| 10. Full QFA conclusion | Full zero-data strict/closed root, including own-trace future velocity uniqueness | General nonzero-data QFA at the frozen cutoff |


The historical corrected root retains class realization, comparison,
Agmon, reference-construction and smoothness inputs, and its old strict cutoff
$M^4/(16\pi^2\nu^5)$. The new spectral proof inhabits one input interface;
it does not discharge the others. Periodic QFB remains an accepted reference
with its original scope. This integration does not assert an A/B equivalence.

## Evidence and retained history

The exact 35 recovered vendor sources are retained with per-file provenance;
33 are active and the original failed multiplier source and barrel remain
inactive. All 495 previously tracked native Lean files and all existing
compiler/dependency/driver policies remain unchanged from the integration basis.

The four earlier attempts are retained under `audits/`: the first exposed
cutoff and upstream multiplier elaboration failures; the second exposed scalar
conversion failures; the third isolated private spectral algebra; the fourth
passed all proofs and audits but was rejected for missing package-index entries.
The accepted run includes the corrected index. No failed run was promoted.

See [QFA_FOUNDATIONS_A_TIER.txt](QFA_FOUNDATIONS_A_TIER.txt) for the complete
accepted native name register and [INTEGRATION_STATUS.json](INTEGRATION_STATUS.json)
for the machine-readable boundary. Evidence-only later commits do not replace
the tested revision or claim a new compiler run.
