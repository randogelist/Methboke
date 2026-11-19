# Next mathematical layer: source review and prepared input adapter

Date: 2026-11-19. Reviewed repository base:
`randogelist/Methboke@bfc9c6f39230121f6a269f65e22784597ce0d4cd`.
Method: source reading and nonexecuting static inspection only. No Lean, Lake,
kernel audit, executable control test or external verification was performed
for this layer. The fixed finite-cap goal and all ten obligation statuses are
preserved.

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

## Fixed R0 finite-cap path: separate localization gap

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
finite cap is not justified. A genuine finite-front localization of the
physical relative-energy chain is needed. The scalar theorem
`CRITICAL_RELATIVE_ENERGY_ZERO_OF_LOCAL_ADMISSIBLE_TRACE` is useful only after
that physical relative-energy inequality, local integrability, and limiting
initial trace have been supplied. A proof of the scalar Gronwall implication
does not supply those physical hypotheses.

`FiniteFrontTest.lean` now prepares the missing test extension with a smooth
time map, avoiding a zero-extension boundary argument. For a shorter horizon
`0 < t < T`, choose a real bump `b` centered at zero with
`t < rIn < rOut < T`, set `c = T/2` and
`rho(r) = c + b(r)*(r-c)`. Every positive `rho(r)` lies strictly in `(0,T)`;
near every time in `[0,t]`, `rho(r)=r`. The physical field
`phi(r,x)=u(rho(r),x)` is therefore a global positive smooth solenoidal test,
with time-neighborhood equality to `u` through the shorter horizon and near
zero. It preserves the initial trace without asserting NSE after `t`.
The compact-inner-window form follows. A separate prepared helper transfers
the literal `timeDerivative` across time-neighborhood equality.

The pinned Mathlib source
`Mathlib/Analysis/Calculus/BumpFunction/Basic.lean` provides
`ContDiffBump.contDiff`, `support_eq`, `tsupport_eq`,
`eventuallyEq_one_of_mem_ball`, and `zero_of_le_dist`. These signatures were
read at revision `db584cd6d46c92f209a44c0f1c829460d327499d`; they provide the
cutoff ingredients. The new extension source awaits external verification.
The already prepared `MethbokeAddon.WeakFouriermanB.local_nse_energy_identity` supplies the
finite-front classical energy side. After the extension is proved, the next
separate step is to localize the actual weak/classical cross identity.

`CompactCylinderSerrin.lean` prepares four further independent R0 input
lemmas. Joint continuity of the actual velocity on
`Icc 0 tau × unitCube` gives a compact uniform bound `M`. The actual slice
eLpNorm at exponent six is dominated by that of the scalar constant `M`,
whose finiteness is proved using the cube's finite measure before applying
`ENNReal.toReal_mono`. The front's established time measurability restricts
to `Ioc 0 tau`; finite time measure and `MemLp.of_bound` yield actual
L4-time/L6-space membership for `0 < tau < Tcap`. No Fourier budget or
Serrin conclusion is assumed. The closed-cylinder continuity premise is
precisely the regularity supplied by an admitted analytic cylinder. These
four lemmas remain candidates pending matching external verification.

## Independent prepared WFB-08 input adapter

`SmoothDatum.lean` is a small, independent source candidate. It uses actual
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
seven prepared declarations, not seven accepted milestones. It is staged
outside active Material discovery; activation requires registering its source,
wrapper, exact-type audits and fresh theorem-level axiom reports, followed by
matching authorized external cached verification.

The source reuses `physical_constant_pairing_coordinate` and
`physical_inner_congr_left_ae` from QuasiFeffermanB, the literal pressure
gradient cancellation from `CriticalSmoothCancellation`, and the actual
representative-norm identity from `CriticalRelativeEnergyIntegrable`.
It assumes only `SmoothSigmaZero a` and, for weak existence, `nu > 0`.

Status: **prepared candidate; no new A-tier declaration, complete obligation,
root closure, or chat sign**.
