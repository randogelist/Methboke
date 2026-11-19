# Finite-window physical comparison: exact dependency map

Status: source preparation and static review only, 2026-11-19. No local Lean,
Lake, kernel audit or executable project test was run. These candidates do not
complete WFB-08 or the finite-cap root without matching external evidence and
the remaining physical adapters.

The retained `CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON` has a finite conclusion
but global-positive classical-equation and pressure hypotheses. Its proof can
be localized while retaining a globally admissible smooth velocity **test**.
That test is not required to solve NSE outside the comparison interval.

| Existing declaration | Actual use of the global premise | Finite-window treatment |
|---|---|---|
| `CriticalIntegratedWeakMomentum.test_integrable` and `.momentum`, `CriticalWeakMomentum.lean` | These genuinely quantify over globally positive-time smooth solenoidal tests | Construct a test by smooth time clamping, preserving the original front near every time in `(0,T]`; retain the literal weak-momentum fields unchanged |
| `CRITICAL_WEAK_CLASSICAL_CROSS_IDENTITY`, same file | Pressure regularity, periodicity and NSE are used only at `r in Icc s t` | Prepared `finite_window_weak_classical_cross_identity`; its conclusion contains actual integrability and the physical cross integral, without an assumed relative inequality |
| `critical_smooth_energy_pairing`, `CRITICAL_SMOOTH_NSE_ENERGY_HAS_DERIV`, `CRITICAL_SMOOTH_NSE_ENERGY_IDENTITY`, `CriticalSmoothEnergy.lean` | Pointwise pairing uses the equation only at the differentiation time; the integral proof uses times inside `[s,t]` | Localize the pairing and energy identity to `Icc s t`. Alternatively transfer the already prepared `local_nse_energy_identity` for the original finite front |
| `CRITICAL_LH_SMOOTH_RELATIVE_ENERGY_RAW`, `CriticalRelativeEnergy.lean` | Its two nonlocal calls are the classical energy and cross identities; all other field/gradient manipulations are on `[s,t]` | Replace those calls with the two localized identities. Keep the actual LH energy inequality at the admissible start time and derive the relative inequality |
| `CRITICAL_LH_SMOOTH_RELATIVE_ENERGY_TRANSPORT`, `CriticalRelativeEnergyTransport.lean` | Only its call to RAW needs the global PDE hypotheses | Replace RAW; retain exact spatial nonlinear polarization and rough transport skew identities |
| `CriticalLerayHopf.relativeEnergy_intervalIntegrable` and `CRITICAL_RELATIVE_ENERGY_PRODUCT_INTERVAL_INTEGRABLE`, `CriticalRelativeEnergyIntegrable.lean` | Depend on the global admissible smooth test, not on a global NSE equation | Reuse unchanged for the clamped test; they already derive integrability from actual LH energy and momentum |
| `CRITICAL_LERAY_HOPF_SERRIN_COMPARISON_ON`, `CriticalSerrinUniqueness.lean` | Besides the relative-transport call, the proof uses global smooth-test facts, original trace, and actual finite Serrin integrability | Prepared `finite_window_leray_hopf_serrin_comparison` with pressure and NSE only on `Ioc 0 T`; it retains the complete admissible-time, transport-estimate and Gronwall proof |

## Prepared signatures

`FiniteWindowCrossIdentity.lean` supplies the source candidate

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

`FiniteWindowSerrinComparison.lean` supplies the source candidate

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
needed for this construction. `FiniteFrontTest.lean` is being prepared with
this stronger positive-time construction.

Remaining assembly work is explicit: transfer time derivatives from eventual
equality, transfer the same spatial slices and their operators, transport the
trace and finite Serrin norm, and invoke the localized comparison. Thereafter
pointwise overlap, normalized-pressure equality and smooth gluing are still
separate finite-cap obligations. None is replaced by a desired-output field.
