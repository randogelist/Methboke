# Mathematical source review and accepted R0 adapters

Date: 2026-11-19. Current external acceptance:
`93ca8a57536512556ec36717ee933ea52db283bf`,
[run 44549257770](https://github.com/randogelist/Methboke/actions/runs/44549257770).
The [matching record](../../../../../audits/material-93ca8a5/summary.json) verifies
321 modules (303 reused, 18 freshly compiled), all 33 fresh endpoint packages,
161 declaration audits plus cutout and 183 controls, with standard axioms only.
The exact `D_Q_subset_R_nu` and classical/two-sided analytic finite-cap roots
are accepted; both velocity and normalized pressure are preserved on the
admitted front. Universal R1, the remaining eight WFB contextual obligations
and exact WFB root remain open.

Historical source-review base:
`randogelist/Methboke@bfc9c6f39230121f6a269f65e22784597ce0d4cd`.
The initial review used source reading and nonexecuting static inspection only;
it did not itself supply compiler evidence. Later acceptance is identified
above and below. No Lean, Lake, kernel audit or executable control test ran
locally during source preparation or repair.

## WFB-03: first formalization obstruction

Required edge: from arbitrary smooth periodic divergence-free mean-zero datum
with physical H1 norm bounded by R, construct an actual local strong NSE
solution with normalized pressure for a positive duration depending only on
nu > 0 and R.

The inspected library supplies these genuine, narrower statements:

| Source declaration | Exact available scope | Missing requirement |
|---|---|---|
| `SingularClosure.finiteGalerkinRhs_uniform_local_time`, `Material/_vendor/SingularClosure/GalerkinExistence.lean` | For each `nu, N, R`, a positive duration for the finite-dimensional Fourier ODE, uniform over its finite-state ball | Duration may depend on cutoff N; finite-state radius is not a uniform physical H1 estimate |
| `SingularClosure.CRITICAL_GALERKIN_GLOBAL_EXISTS_UNIQUE`, `CriticalGalerkin.lean` | Global existence and forward uniqueness for each fixed-cutoff real solenoidal Galerkin system | A physical strong limit, its H1 bounds and pressure reconstruction are absent from this theorem |
| `SingularClosure.fourierSobolevRhs`, `FourierSobolevRhs.lean` | Actual infinite RHS from `TorusSobolev (r + 2)` into `TorusSobolev r`, with smoothness and coefficient identity | It is not a same-space locally Lipschitz vector field to which the ordinary Banach ODE existence theorem directly applies |
| `SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL`, `CubicBudget.lean` | Scalar differential inequality plus an explicitly assumed square budget gives an enstrophy-type bound | It neither proves the physical PDE enstrophy inequality nor constructs a solution/restart |

The first blocked implication is therefore:

```text
fixed-cutoff ODE existence
  -/-> cutoff-uniform H1 local physical NSE existence.
```

Discharging it requires either a genuinely matching formal local H1 theorem,
or new cutoff-uniform local estimates, compactness/convergence, strong trace,
physical NSE and pressure construction. No such ready-made theorem was found
in the inspected pinned vendor tree. This is a statement about that source
search, not a mathematical nonexistence claim. The classical local theorem
already cited in the cumulative B-tier argument remains a legitimate
mathematical input, but is not a compiled Lean theorem.

No WFB-05 maximal-trajectory, WFB-06 continuation, WFB-07 strict-overlap, or
WFB-10 root derivation is advanced past this missing edge. No continuation
field or admission axiom has been introduced.

## Fixed R0 finite-cap path: resolved localization gap

An already admitted finite analytic solution does not require WFB-03 merely
to exist. It still requires identification with the original Leray--Hopf path
on the finite front.

`SingularClosure.CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON`, in
`Material/_vendor/SingularClosure/CriticalSerrinUniqueness.lean`, concludes
agreement on `Ioc 0 T`, but its inputs require
`CriticalPositiveSolenoidalTest u` and the actual NSE equation for **all**
positive times. The name and finite conclusion do not remove these global
positive-time hypotheses. `CriticalPositiveSolenoidalTest` itself requires
joint smoothness throughout positive spacetime.

Consequently, applying it directly to a solution available only before a
finite cap is not justified. The accepted finite-front localization of the
physical relative-energy chain supplies this missing interface. The scalar theorem
`CRITICAL_RELATIVE_ENERGY_ZERO_OF_LOCAL_ADMISSIBLE_TRACE` is useful only after
that physical relative-energy inequality, local integrability, and limiting
initial trace have been supplied. A proof of the scalar Gronwall implication
does not supply those physical hypotheses.

`FiniteFrontTest.lean` supplies the accepted test extension with a smooth
time map, avoiding a zero-extension boundary argument. For a shorter horizon
`0 < t < T`, choose a real bump `b` centered at zero with
`t < rIn < rOut < T`, set `c = T/2` and
`rho(r) = c + b(r)*(r-c)`. Every positive `rho(r)` lies strictly in `(0,T)`;
near every time in `[0,t]`, `rho(r)=r`. The physical field
`phi(r,x)=u(rho(r),x)` is therefore a global positive smooth solenoidal test,
with time-neighborhood equality to `u` through the shorter horizon and near
zero. It preserves the initial trace without asserting NSE after `t`.
The compact-inner-window form follows. A separate accepted helper transfers
the literal `timeDerivative` across time-neighborhood equality.

The pinned Mathlib source
`Mathlib/Analysis/Calculus/BumpFunction/Basic.lean` provides
`ContDiffBump.contDiff`, `support_eq`, `tsupport_eq`,
`eventuallyEq_one_of_mem_ball`, and `zero_of_le_dist`. These signatures were
read at revision `db584cd6d46c92f209a44c0f1c829460d327499d`; they provide the
cutoff ingredients. The extension and finite-window physical comparison chain
were accepted at `67f7663` and freshly audited at `93ca8a5`. The accepted
`MethbokeAddon.WeakFouriermanB.local_nse_energy_identity` supplies the
finite-front classical energy side; the localized cross identity and relative
energy theorems supply the other physical comparison steps.

`CompactCylinderSerrin.lean` supplies four accepted R0 input
lemmas. Joint continuity of the actual velocity on
`Icc 0 tau × unitCube` gives a compact uniform bound `M`. The actual slice
eLpNorm at exponent six is dominated by that of the scalar constant `M`,
whose finiteness is proved using the cube's finite measure before applying
`ENNReal.toReal_mono`. The front's established time measurability restricts
to `Ioc 0 tau`; finite time measure and `MemLp.of_bound` yield actual
L4-time/L6-space membership for `0 < tau < Tcap`. No Fourier budget or
Serrin conclusion is assumed. The closed-cylinder continuity premise is
precisely the regularity supplied by an admitted analytic cylinder. These
four lemmas passed with the complete R0 layer at `93ca8a5`.

`InitialFrontAdmission.lean` supplies the accepted admission adapter for the
literal `InitialClassicalFront` contract in `FiniteCapGluing.lean`. Spatial
restriction at zero derives `SmoothSigmaZero a`. Compact domination proves
continuity of the actual integral `E(t)=integral |u(t)-a|^2` down to zero,
where the initial equation gives `E(0)=0`. Finite slice L2 membership and the
existing exact norm-square identity give
`eLpNorm(u(t)-a,2)=ofReal(sqrt(E(t)))`, proving the literal strong initial
trace. The conversion to `LocalPhysicalNSEFront` therefore adds no trace
premise. Compact Serrin and finite-window comparison then identify every
original LH path with the admitted front before its cap. Q01 provides one
such original path. These nine accepted theorems assume existence of the
actual initial classical pair; they do not construct it from arbitrary
smooth data or assert universal admission.

## Accepted WFB-08 input adapter; whole obligation remains open

`SmoothDatum.lean` is a small, independently accepted source module. It uses actual
periodic integration by parts and the original Q01 existence theorem to prove:

1. Smooth physical data are in the literal cube L2 space.
2. `criticalL2Representative a` equals `a` almost everywhere.
3. Every constant coordinate pairing vanishes for mean-zero data.
4. `EnergySigmaZero (criticalL2Representative a)` follows from
   `SmoothSigmaZero a`, with no additional analytic certificate.
5. Its squared L2 norm equals `physicalEnergy a`.
6. The literal QFB cutoff equals
   `(physicalEnergy a)^2 / (8*pi^2*nu^5)`.
7. Q01 yields an original `CriticalLerayHopf` trajectory and the actual initial
   equality to `a` almost everywhere.

This is only the datum-admission/existence portion of WFB-08. It does not
identify a strong trajectory or complete that contextual obligation. It has
seven accepted declarations, not seven complete contextual obligations. Its
active source, wrapper, exact-type assertions and theorem-level axiom reports
first passed at `67f7663` and passed freshly again in the `93ca8a5` package.

The source reuses `physical_constant_pairing_coordinate` and
`physical_inner_congr_left_ae` from QuasiFeffermanB, the literal pressure
gradient cancellation from `CriticalSmoothCancellation`, and the actual
representative-norm identity from `CriticalRelativeEnergyIntegrable`.
It assumes only `SmoothSigmaZero a` and, for weak existence, `nu > 0`.

Status: **accepted input component; no completion of the whole WFB-08
obligation or exact WFB root**.


## Accepted frozen R0 data classes

`AnalyticTwoSidedCap.lean` and `R0DataAdmission.lean` are now registered in
`Material` as `R0AnalyticTwoSidedCap` and `R0DataAdmission`. Their five and two
public declarations each have an independent exact-signature assertion and
fresh theorem-level type/axiom audit. Candidate and active proof bytes match.

The complete accepted scope at `93ca8a5` is 321 modules, 33 endpoint packages
and 161 declaration audits plus the QFB cutout. Previous declarations, compiler/
dependency pins and driver behavior were preserved. Matching external cached
compilation and all required fresh type/axiom audits passed. No local Lean or
executable tests ran.

The first module states actual NSE on the full two-sided analytic cylinder
using the ordinary time derivative. It derives equality with the physical
forward derivative for nonnegative times, including zero, and applies the
accepted finite-cap root. The second module defines the frozen classes with
the explicit zero branch and the genuine nonzero double-cutoff cap. Its
`D_Q_subset_R_nu` theorem proves the R0 inclusion from those premises; it does
not assert that arbitrary smooth data or every local analytic germ belongs
to `D_Q`. Universal extension R1 remains unresolved.


## Historical external R0 checks and localized repairs

Run `44543421609` at `0ddd2d67` stopped before audits at two rewrite matches
in `FiniteCapGluing` and `PressureUniqueness`. It did not accept R0; the accepted
baseline at that time was `67f7663`, with 303 modules, 24 packages and 120
declarations plus cutout. Candidate and active proof corrections preserved
every statement: the splice-left proof made the pointwise conditional explicit
before `if_pos`, and the pressure proof repaired the reported rewrite match.
Hashes, closures and fingerprints were synchronized. Adding the two frozen
data-class adapters expanded the scope to 321/33/161.

Run `44545010863` at `c6e039da` compiled those corrections but stopped in
InitialFrontAdmission at filter-membership field notation and composition
expansion. Typed eventual bounds via `nhdsWithin_le_nhds` and explicit
`Function.comp_def` repaired only the reported proof sites.

Run `44547124107` at `d2c0259` compiled all 321 modules and passed 19 audit
packages, including the literal R0 root. Its pressure audit stopped because
an open command named an absent, unused namespace. Removing that namespace
preserved the nine exact-type assertions and all type/axiom sentinels.

These failed attempts skipped recovery and did not replace accepted caches.
The complete unchanged scope subsequently passed at `93ca8a5` in run
`44549257770`, with every audit fresh and successful publication. Historical
preparation labels in source/provenance records remain historical; current
acceptance is determined by this matching external evidence.
