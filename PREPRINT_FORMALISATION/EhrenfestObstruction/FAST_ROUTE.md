# Shortest identified Lean route

**Version 0.3.0 — B-tier derivation and proposed layout only.** The frozen implication and its stopped premise are unchanged. This is a reduction in new proof infrastructure; no compiler timing or global runtime optimality is claimed.

The scalar root needs **nine of the 31 planned modules**. The 31-file inventory includes the original stronger milestones, the new shorter proof and an optional full import bundle. Only the nine-module source closure should enter the first root activation. No Lean source is activated by this document.

## Two mathematical reductions

### 1. One cutoff and one mean-value comparison

Suppose the stopped premise holds for one fixed smooth datum. Set `T=1/gamma`. Under a hypothetical global smooth solution, prove only

```text
exists C, eventually n,
  forall t in [0,T], e_n(t) <= C.
```

Choose one index beyond the stopped and stability indices with `R_n>C`. For every `t<T`, all earlier times satisfy `e_n(s)<=C<R_n`, so the literal `PreHit` guard holds. Consequently `v_n'=c_n<=-gamma` throughout `(0,T)`. The pinned Mathlib theorem `exists_hasDerivAt_eq_slope` gives

```text
v_n(T) <= v_n(0)-gamma*T <= 0,
```

contradicting `0<v_n(T)`. Both endpoint continuity and `v_n(0)<=1` follow from the actual canonical reciprocal. There is no need for the stopped inequality or an ordinary derivative at `T`.

This proof uses no threshold hitting-time definition, initial bound uniform in cutoff, divergent supremum, or finite maximum over small cutoffs. E07's hitting theorem and E08's threshold escape remain valid independent milestones.

### 2. Eventual H1 control instead of full H2 error convergence

For an actual smooth solution `U` on a front `[0,S)`, take `0<=T<S`. Write

```text
v_N=P_N U,  r_N=U-v_N,  w_N=u_N-v_N,  N=n+1,
f_N=P_N P_Leray(B(r_N,U)+B(v_N,r_N)).
```

The exact error equation is

```text
w_N' + nu*A*w_N
  + P_N P_Leray(B(w_N,w_N)+B(v_N,w_N)+B(w_N,v_N)) = f_N,
w_N(0)=0.
```

For the primary source-grounded route choose finite `K>=1` controlling the actual reference's H3 norm and first spatial derivatives on `[0,T]`. Smoothness gives this on the strict subslab; it is no new hypothesis on the stopped datum. Use the existing finite Fourier H2-to-coefficient-l1 estimate on coefficients and their first-derivative multipliers to get

```text
||v_N||_infinity + ||grad v_N||_infinity <= C*K.
```

Use the existing Sobolev multiplier norm estimate with the actual cutoff complement to prove

```text
||r_N||_H1 <= C*K/N,   ||f_N||_2 <= C*K^2/N.
```

For the residual, use only `||B(r,U)||2 <= ||r||2 ||grad U||infinity` and `||B(v,r)||2 <= ||v||infinity ||grad r||2`. The coefficient-l1 and tail sources still need finite-mode, componentwise and physical-normalization adapters; they are not already the displayed final estimates.

Put `D_N=||grad w_N||2^2` and `Z_N=||A w_N||2^2`. Pair the finite error equation with `A w_N`; Fourier and Leray projections disappear under this pairing. Its self-interaction has exactly the sign of

```text
integral convection(w_N) dot laplacian(w_N).
```

Apply the existing **arbitrary-field** `PHYSICAL_NONLINEAR_ABSORPTION`, with a viscosity fraction, to bound that self-interaction by a small multiple of `nu*Z_N` plus `C_nu*D_N^3`. Its hypotheses are smoothness, periodicity and mean zero; `w_N` need not solve NSE. The source theorem is one-sided, which is exactly sufficient for this signed term.

The two mixed terms are bounded by

```text
(||grad v_N||infinity ||w_N||2
 + ||v_N||infinity ||grad w_N||2) * sqrt(Z_N).
```

Mean-zero Poincare and Young absorb them, together with the residual, into the remaining viscosity budget. Thus

```text
D_N' <= C_(nu,K)*(D_N+D_N^3) + C_(nu,K)/N^2,
D_N(0)=0.
```

On `D_N<=1`, apply Gronwall to obtain `D_N(t)<=C_(nu,K,T)/N^2`. For sufficiently large `N` the bound is strictly below one, so continuity excludes an error-bootstrap exit at `D_N=1`. This is an internal scalar bootstrap; it is not construction of the stopped condition's threshold hit. Therefore

```text
e_N(u_N(t)) <= ||grad v_N(t)||2^2 + D_N(t) <= K^2+1
```

eventually in cutoff and uniformly on `[0,T]`. This is exactly the missing bound in the scalar contradiction.

A reference H2 bound is mathematically sufficient if one instead uses H2-to-Linfinity, H1-to-L6 and gradient-H2-to-L3 estimates. The primary plan uses the located finite Fourier l1 infrastructure because it avoids adding that embedding layer. Actual smoothness supplies H3 without changing the theorem's input class. No runtime comparison has been measured.

## Minimal source closure

All paths below are proposed under `Material/MethbokeAddon/EhrenfestObstruction/`.

| Module | New output | Reuse / scope |
|---|---|---|
| `Definitions.lean` | Literal canonical family, reciprocal, drift, guard and public predicates | Preserve viscosity, one fixed datum and cutoff `n+1`. |
| `ReciprocalDrift.lean` | Exact derivative and `0<V<=1` | Existing coefficient enstrophy identity; inverse chain rule. |
| `SlabDescent.lean` | Terminal comparison from interior rate bound | Narrow import `Mathlib.Analysis.Calculus.Deriv.MeanValue`; explicit derivative rate. |
| `ClosedSlab.lean` | Actual smooth reference on `[0,T]` from a front with `T<S` | Actual physical PDE and compact trace bounds, no Galerkin conclusion in the definition. |
| `SmoothReference.lean` | Uniform projected C1 bound, H1 tail and L2 residual | Finite Fourier l1, multiplier norm and componentwise adapters. |
| `H1Error.lean` | Finite-coefficient error enstrophy identity and scalar differential inequality | Physical nonlinear absorption, Poincare, elementary mixed L2 estimates. |
| `EventualEnstrophyBound.lean` | Eventual slab bound from the actual front | Scalar bootstrap/Gronwall only; omit the finite-small-cutoff maximum. |
| `DynamicalRoot.lean` | Single-cutoff contradiction | Mean value and literal stopped predicate; no E08 or full E09 imports. |
| `Root.lean` | Frozen `EHRENFEST_OBSTRUCTION` | Imports only `DynamicalRoot`. |

Differentiate the finite weighted coefficient sum for `D_N`. Derive each actual-reference Fourier coefficient derivative from its smooth PDE and the spatial integral. Then use physical Parseval identities. This avoids introducing a general Sobolev-valued time-differentiation API. The actual-NSE enstrophy theorem cannot simply be applied to the forced error `w_N`; its finite-coefficient error identity is new work.

[FAST_INTERFACES.lean.txt](FAST_INTERFACES.lean.txt) gives the exact proposed contracts. [MODULE_PLAN.json](MODULE_PLAN.json) records all imports, critical-path flags and package mappings. `Root.lean` must never import the optional `All.lean` bundle.

## Early exact operator theorem and full translation

The first operator theorem can be proved on native `TestFunction` complex-linear maps. For smooth real vector field `b` and any smooth zero-order coefficient `a`, define

```text
H0 psi = -i*hbar*(D psi[b] + a*psi).
```

The product rule gives `(i/hbar)[H0,M_g]=M_(Dg[b])`; the zero-order term cancels. Specialize to `a=div(b)/2` later. This removes divergence, a unitary group and self-adjointness from the early algebra proof. The finite-N reciprocal multiplier is the literal rational drift already used by the scalar theorem.

The full Hilbert-space milestone still requires the actual dense core embedding, complete flow, Jacobian half-density transport, strong continuity, self-adjoint generator and domain equality. Fixed-cutoff multiplier bounds and core algebra do not establish these results. Preserve the v0.2 direct generator/resolvent and time-convolution core construction.

## Activation and acceptance

The shortest proposed order is: scalar definitions/comparison and H1 error work in parallel; exact scalar root; independent core commutator; full operator translation; retained stronger hitting/escape/H2-convergence results.

Do not activate all 31 planned sources for the first root run. The native pipeline indexes every Lean file under `Material`; activate only a coherent registered closure with exact hashes, imports, package manifests and fresh public-declaration audits. Preserve the existing cache identity, compiler, vendor and Mathlib pin. Use narrow imports and the existing native workflow. No local Lean, Lake or kernel run is allowed.

E10's literal implication can be accepted while other milestones remain open. Full workstream acceptance still means every one of the ten original scopes has passed. E09's full H2-convergence statement has not been silently weakened: its shorter `E09.bound` helper is separately tracked. All current results are written B-tier arguments; no new Lean endpoint is accepted and no stopped-bound witness is constructed.
