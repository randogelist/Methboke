# Finite-window physical comparison: exact dependency map

Status: externally accepted finite-front comparison at `67f7663`, freshly
audited in the complete R0 package at `93ca8a5`, 2026-11-19. See
[run 44549257770](https://github.com/randogelist/Methboke/actions/runs/44549257770)
and its [matching evidence](../../../../../audits/material-93ca8a5/summary.json):
321 modules, 33 fresh packages, 161 declarations plus cutout, standard axioms
only. Local preparation used no Lean, Lake, kernel audit or executable tests.
The exact R0 inclusion is accepted; WFB-08 as a whole, the other remaining WFB
obligations, the exact WFB root and universal R1 remain open.

The retained `CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON` has a finite conclusion
but global-positive classical-equation and pressure hypotheses. Its accepted
localized proof retains a globally admissible smooth velocity **test**.
That test is not required to solve NSE outside the comparison interval.

| Existing declaration | Actual use of the global premise | Finite-window treatment |
|---|---|---|
| `CriticalIntegratedWeakMomentum.test_integrable` and `.momentum`, `CriticalWeakMomentum.lean` | These genuinely quantify over globally positive-time smooth solenoidal tests | Construct a test by smooth time clamping, preserving the original front near every time in `(0,T]`; retain the literal weak-momentum fields unchanged |
| `CRITICAL_WEAK_CLASSICAL_CROSS_IDENTITY`, same file | Pressure regularity, periodicity and NSE are used only at `r in Icc s t` | Accepted `finite_window_weak_classical_cross_identity`; its conclusion contains actual integrability and the physical cross integral, without an assumed relative inequality |
| `critical_smooth_energy_pairing`, `CRITICAL_SMOOTH_NSE_ENERGY_HAS_DERIV`, `CRITICAL_SMOOTH_NSE_ENERGY_IDENTITY`, `CriticalSmoothEnergy.lean` | Pointwise pairing uses the equation only at the differentiation time; the integral proof uses times inside `[s,t]` | Accepted `finite_window_smooth_nse_energy_identity` localizes to `Icc s t`; `local_nse_energy_identity` supplies the original finite-front form |
| `CRITICAL_LH_SMOOTH_RELATIVE_ENERGY_RAW`, `CriticalRelativeEnergy.lean` | Its two nonlocal calls are the classical energy and cross identities; all other field/gradient manipulations are on `[s,t]` | Accepted localized RAW theorem uses the two localized identities and actual LH energy inequality to derive the relative inequality |
| `CRITICAL_LH_SMOOTH_RELATIVE_ENERGY_TRANSPORT`, `CriticalRelativeEnergyTransport.lean` | Only its call to RAW needs the global PDE hypotheses | Accepted localized transport theorem uses localized RAW and retains exact spatial polarization and rough transport skew identities |
| `CriticalLerayHopf.relativeEnergy_intervalIntegrable` and `CRITICAL_RELATIVE_ENERGY_PRODUCT_INTERVAL_INTEGRABLE`, `CriticalRelativeEnergyIntegrable.lean` | Depend on the global admissible smooth test, not on a global NSE equation | Reuse unchanged for the clamped test; they already derive integrability from actual LH energy and momentum |
| `CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON`, `CriticalSerrinUniqueness.lean` | Besides the relative-transport call, the proof uses global smooth-test facts, original trace, and actual finite Serrin integrability | Accepted `finite_window_leray_hopf_serrin_comparison` with pressure and NSE only on `Ioc 0 T`; it retains the complete admissible-time, transport-estimate and Gronwall proof |

## Accepted interfaces

`FiniteWindowCrossIdentity.lean` supplies the accepted declaration

```text
finite_window_weak_classical_cross_identity
  nu v phi p (hv : CriticalIntegratedWeakMomentum nu v)
  (hphi : CriticalPositiveSolenoidalTest phi)
  s t (hs : 0 < s) (hst : s <= t)
  (hp,hpp,hNSE restricted to Icc s t)
```

Its only copied private helpers are elementary, reproved integral linearity in
the smooth second argument. No custom axiom, certificate, or substitute
relative-energy premise occurs.

`FiniteWindowSerrinComparison.lean` supplies the accepted declaration

```text
finite_window_leray_hopf_serrin_comparison
  nu hnu a0 v u G p hv hu T hT
  (hp,hpp,hNSE restricted to Ioc 0 T)
  (hu_trace : original strong physical L2 initial trace)
  (hSerrin : actual L4-time/L6-space norm on Ioc 0 T)
```

The output is physical almost-everywhere equality `v t = u t` on the cube for
every `t in Ioc 0 T`. The only substantive change inside the retained comparison
proof is the relative-transport call on `[epsilon_n,t]`; set inclusion into
`Ioc 0 T` is proved explicitly. Its dependency
`finite_window_lh_smooth_relative_energy_transport` has the fixed parameter
order `nu hnu a0 v u G p hv hu s t hs hst hp hpp hNSE henergy`.

## Test extension and the initial trace

A clamp that is constant near time zero does not retain the initial trace, so
it cannot simply be passed to the global comparison theorem. It is sufficient
for separately localized estimates on each `[epsilon_n,t]`.

For one test covering the whole comparison front, only positive-time smoothness
is needed. Choose `T < rIn < rOut < Tcap`, a smooth bump `chi` centered at zero
with these radii, and `c in (0,Tcap)`. Define

```text
rho(r) = c + chi(r) * (r-c),   phi(r,x) = u(rho(r),x).
```

For every `r>0`, `rho(r)` lies in `(0,Tcap)`: where the bump is nonzero, it is
a convex combination of `r in (0,rOut)` and `c`; elsewhere it is `c`.
Near every point of `[0,T]`, the bump is one, so `rho(r)=r`. Thus the test
preserves the original positive initial trace and Serrin norm as well as all
local derivatives. No analyticity at zero and no global NSE extension is
needed for this construction. `FiniteFrontTest.lean` implements this
positive-time construction; its five declarations were accepted at `67f7663`.

The accepted `LocalFrontIdentification.lean` assembly transfers time derivatives
from eventual equality, spatial slices and operators, the initial trace and
finite Serrin norm, then invokes the localized comparison. The R0 layer accepted
at `93ca8a5` supplies compact-cylinder Serrin bounds, strong initial trace,
pointwise overlap, normalized-pressure equality and smooth gluing. Its classical
and two-sided analytic roots preserve both velocity and pressure on `[0,T)`;
`D_Q_subset_R_nu` handles the zero branch and actual double-cutoff analytic cap.
No desired-output field replaces these derivations. An actual admitted cap
remains explicit, so neither universal R1 nor the complete WFB criterion follows.
