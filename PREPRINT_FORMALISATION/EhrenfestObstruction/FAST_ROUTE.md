# Implemented scalar-root route

The project goal is `∀ ν>0, StoppedCommutatorBound ν → ¬ NSE_B ν`.
The literal stopped premise and all public theorem types are unchanged.
At `22431f032c868b8de1526767d7d32a2639f6a9ee`, the scalar implementation is complete;
[run 44641040255](https://github.com/randogelist/Methboke/actions/runs/44641040255)
passed the full compiler/type/axiom and publication/final-acceptance gates.
[Matching evidence](../../audits/material-22431f03-accepted/summary.json) accepts
E09.bound and exact conditional E10, including 75 new declarations; all 183
scoped Ehrenfest declarations are now accepted. The full operator and H2
milestones and the stopped witness remain separate and open.

## Same datum and exact drift

Use the canonical solution `u_n` at physical cutoff `N=n+1`. Fix one smooth
solenoidal mean-zero datum `a`, viscosity `ν>0`, `e_*>0`, `γ>0`, and positive
thresholds `R_n→∞`. Define

```text
e_n = coefficientDissipation(N,u_n)/2,
V_n = (1+e_n/e_*)^(-1),
c_n = (ν Z_n + Pwr_n)/(e_* (1+e_n/e_*)^2),
T = 1/γ.
```

The native identity is `e_n′=-ν Z_n-Pwr_n`, so `V_n′=c_n` and `0<V_n≤1`.
The stopped predicate asserts `c_n≤−γ` eventually in cutoff, only for
`t<T` when all `e_n(s)<R_n` for `0≤s≤t`. No hitting-time construction is needed.

## Actual-front H1 error bound

Assume an actual `InitialClassicalFront ν S a U P` with `T<S`. Define
`v_n=P_N U`, `r_n=U−v_n`, `w_n=u_n−v_n`, and `D_n=||∇w_n||₂²`.
The spatial differential below uses the operator norm; the integrated
gradient-square quantities use the summed component norm. The actual smooth
front supplies `M,K≥1` and finite `K_D`, independent of cutoff, such that

```text
||v_n||∞, ||d v_n||∞, ||d U||∞ ≤ M,
||r_n||₂²+||∇r_n||₂² ≤ 12 K²/N²,
||∇v_n||₂² ≤ K_D.
```

For `B(x,y)=(x·∇)y` and `Π_N=P_N P_Leray`, the residual and error equation are

```text
R_n^res = B(r_n,U)+B(v_n,r_n) = B(U,U)−B(v_n,v_n),
w_n′+ν A w_n+Π_N[B(w_n,w_n)+B(v_n,w_n)+B(w_n,v_n)] = Π_N R_n^res,
w_n(0)=0.
```

The coefficient derivatives and Leray pressure cancellation are derived from
the actual equations. The forced error is not treated as an unforced NSE
solution. The physical residual estimate gives

```text
||R_n^res||₂² ≤ 6 M² (||r_n||₂²+||∇r_n||₂²) ≤ 72 M² K²/N².
```

Arbitrary-field nonlinear absorption, Poincare and Young inequalities give

```text
D_n′ ≤ (C₀/ν³)D_n³ + (24 M²/ν)D_n + (6/ν)||R_n^res||₂².
C = C₀/ν³ + 24 M²/ν + 1 > 0,
A₀ = 432 M² K²/ν > 0,
ε_n = A₀/N² → 0,
D_n′ ≤ C(D_n+D_n³)+ε_n.
```

Closed-slab coefficient continuity and finite summation give continuity of
`D_n`; the derivatives are required only on `(0,T)`. For sufficiently large
`n`, `2 ε_n exp((2C+1)T)≤1`. Use the positive comparison function
`F_n(t)=2 ε_n exp((2C+1)t)`. At a potential contact `D_n=F_n≤1`,

```text
D_n′ ≤ 2C F_n+ε_n < (2C+1)F_n = F_n′.
```

Initial continuity supplies an interior starting point and terminal
continuity gives the endpoint. Thus `D_n≤F_n≤1` on the whole closed slab.
The unit error bound is a conclusion, not an input. Reconstruction yields

```text
e_n(t) ≤ D_n(t)+||∇v_n(t)||₂² ≤ 1+K_D,
exists Cstar, eventually n, forall t in [0,T], e_n(t)≤Cstar.
```

This is exactly `E09.bound`. No full H2 convergence, all-cutoff maximum or
uniform initial enstrophy estimate is needed by the root.

## One cutoff and one scalar contradiction

Intersect the eventual stability bound, the stopped-index bound, and
`R_n>Cstar`. For one resulting index every earlier time stays below `R_n`,
so the literal `PreHit` guard holds at every `t∈(0,T)`. Consequently
`V_n′≤−γ`. Mean-value comparison gives

```text
0 < V_n(T) ≤ V_n(0)−γT ≤ 1−1 = 0.
```

No derivative or stopped-rate assertion at either endpoint is needed.
A hypothetical global smooth pair for the same datum supplies the strict
front `S=T+1`, yielding the exact conditional E10 theorem.

## Source and internal-step mapping

All modules below are under `Material/MethbokeAddon/EhrenfestObstruction/`.
The [cumulative text](../../EHRENFEST_OBSTRUCTION_B_TIER.txt) records the full
INT01–INT12 derivation and explicit assumptions.

| Internal steps | Concrete modules |
|---|---|
| INT01–INT02 | Definitions, ReciprocalDrift |
| INT03–INT04 | SmoothSobolevNorm, FourierL1, ProjectedC1, SmoothReference, FourierTail, PhysicalReferenceTail, ReferenceC1Norm |
| INT05 | ReferenceCoefficientEvolution, ProjectedReferenceEvolution, PressureFourier, ErrorState, ErrorEquation |
| INT06–INT07 | CoefficientError, PhysicalForcing, CrossTransport, CanonicalErrorInequality |
| INT08–INT09 | SmallForcingBootstrap, EventualEnstrophyBound, ErrorSlabBound |
| INT10–INT11 | CanonicalBarrier, SlabDescent |
| INT12 | DynamicalRoot, Root |

The concrete root closure has 25 owned sources. The active Ehrenfest scope
has 30 owned sources and 16 packages; the five additional sources support
hitting/escape or pointwise algebra. The 31 proposed modules and nine logical
blocks in the original design remain historical, not current file counts.
See [COUNT_RECONCILIATION.json](COUNT_RECONCILIATION.json).

## Preserved independent scopes

E07 hitting and E08 escape remain accepted independent results. Full E09
still means `C([0,T];H2)` convergence and its stronger stability statement.
E01–E06 retain the real phase-space/volume adapter, complete flow, half-density
unitary group, generator/core, domain equality and full reciprocal-commutator
interpretation. Pointwise commutator algebra alone does not establish them.
No stopped-bound witness is constructed by the conditional root.

The direct generator/resolvent and time-convolution core design remains in
[OPERATOR_LAYOUT.txt](OPERATOR_LAYOUT.txt). The root source does not import
those optional modules or `All`. Compiler/dependency/audit policies are
unchanged; no local Lean, Lake or kernel execution is permitted.
