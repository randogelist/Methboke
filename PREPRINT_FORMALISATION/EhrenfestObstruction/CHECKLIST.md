# EHRENFEST-OBSTRUCTION: original milestones and scalar-root facets

The project goal is `∀ ν>0, StoppedCommutatorBound ν → ¬ NSE_B ν`.
The stopped hypothesis remains explicit and no satisfying datum is constructed.
E07/E08 retain their earlier acceptance. E09.bound and the exact conditional
E10 theorem are accepted at `22431f032c868b8de1526767d7d32a2639f6a9ee`,
[run 44641040255](https://github.com/randogelist/Methboke/actions/runs/44641040255),
with [matching full evidence](../../audits/material-22431f03-accepted/summary.json).
All 183 scoped Ehrenfest declarations are accepted. This checks three original
full milestones: E07, E08 and E10; it leaves full E09 and E01–E06 unchecked.

The original E01–E10 statements below keep their full scopes. A helper does not
check its parent milestone. E10 can close independently of the full operator
construction and full E09 H2-convergence claim.

- [ ] **E01 — REAL_SOLENOIDAL_GALERKIN_ALGEBRA**
  Identify the real, mean-zero, solenoidal finite Fourier state with V_N; derive polynomial smoothness, projection laws, positive A_N and exact nonlinear energy cancellation.
  B-tier: derived. Sources: ML08, ML12, MLB01. New formal work: Real orthonormal coordinate/volume adapter preserving the existing invariant-state and physical-synthesis semantics.

- [ ] **E02 — COMPLETE_GALERKIN_FLOW**
  Construct a complete jointly smooth flow on R x V_N, inverse/group law and nonsingular Jacobian. Derive forward decay and backward exponential bound with lambda_max(A_N).
  B-tier: derived. Sources: ML01, ML02, ML03, MLB02, MLB03, MLB04, MLB05, MLB06, MLB07, MLB13. New formal work: Backward continuation, smooth dependence and Jacobian identities; current forward existence alone is insufficient.

- [ ] **E03 — HALF_DENSITY_UNITARY_GROUP**
  Construct U_N(t)f=|det D Phi_N^(-t)|^(1/2) f composed with Phi_N^(-t) on L2(V_N;C); prove unitarity, group law, strong continuity and Cc-infinity invariance.
  B-tier: derived. Sources: ML16, ML17. New formal work: Actual L2 operator construction, Jacobian change of variables, density and compact-support continuity.

- [ ] **E04 — SELF_ADJOINT_TRANSPORT_GENERATOR**
  Prove H0_N=-i*hbar*(b_N dot grad+div(b_N)/2) on Cc-infinity is essentially self-adjoint; its closure generates U_N with the specified sign.
  B-tier: derived. Sources: ML15, ML20, OP01–OP12. New formal work: native partially defined operators, direct unitary generator/resolvent construction, adjoint-domain equality and graph-core proof.

- [ ] **E05 — EXACT_HEISENBERG_EHRENFEST_CORRESPONDENCE**
  Prove U_N(t)^* M_g U_N(t)=M_(g composed with Phi_N^t) with natural domains and (i/hbar)[H0_N,M_g]=M_(Dg[b_N]) on the common core; recover observable and localized-state identities.
  B-tier: derived. Sources: ML05, ML10, ML12, ML17, ML18, ML19. New formal work: Domain equality, common-core product rule, L2-normalized smooth packets and fixed-N-first localization.

- [ ] **E06 — RECIPROCAL_ENSTROPHY_COMMUTATOR**
  With e_N=||grad q||^2/2 and Vrec_N=(1+e_N/e_*)^(-1), prove c_N=-(W_N-nu*Z_N)/(e_*(1+e_N/e_*)^2), and its exact bounded-multiplier commutator.
  B-tier: derived. Sources: ML05, ML06, ML08, MLB08, MLB09, MLB18. New formal work: Coefficient/physical normalization, sign, inverse chain rule and bounded commutator extension to the generator domain.

- [x] **E07 — STOPPED_SCALAR_HITTING_BOUND**
  For 0<r<v(0)<=1 and gamma>0, pre-hit drift v prime<=-gamma up to 1/gamma forces a hit of r by (v(0)-r)/gamma<1/gamma.
  Accepted: `stopped_scalar_hitting` and three scalar support declarations in `EhrenfestScalar`, at `40686414`, [run44626474631](https://github.com/randogelist/Methboke/actions/runs/44626474631). [Matching evidence](../../audits/material-40686414-accepted/summary.json) includes exact types, standard axioms and publication acceptance.

- [x] **E08 — CUTOFF_UNIFORM_THRESHOLD_ESCAPE**
  From the explicit StoppedCommutatorBound premise for one fixed smooth datum, derive t_N<1/gamma with e_N(u_N(t_N))>=R_N and hence divergent slab suprema.
  Accepted: the 19 declarations of `EhrenfestEscape`, including `stopped_slab_sup_tendsto_atTop`, at `7908890a`, [run 44635322649](https://github.com/randogelist/Methboke/actions/runs/44635322649). The stopped-bound premise remains explicit.

- [ ] **E09 — SMOOTH_FRONT_GALERKIN_STABILITY**
  An actual smooth solution U on [0,T] implies exact P_Na Galerkin convergence in C([0,T];H2) and uniform H1 there.
  B-tier: derived. Sources: ML03, ML08, MLB11, MLB14, MLB17, MLB19, MLB20. New formal work: New H2 residual/error estimate and first-exit Gronwall bootstrap. Existing conditional H2-budget and local bounds do not supply this full-slab implication.

- [x] **E10 — EHRENFEST_OBSTRUCTION**
  For nu>0, StoppedCommutatorBound nu implies not NSE_B nu; its fixed smooth datum has no smooth continuation through 1/gamma.
  Exact front scope: every actual `InitialClassicalFront` with horizon `S>1/gamma` is excluded.
  Accepted: `EHRENFEST_OBSTRUCTION`, `EHRENFEST_OBSTRUCTION_DYNAMICAL`, `stopped_forbids_initial_front` and `stopped_forbids_global_smooth` in `EhrenfestObstructionRoot`, at `22431f03` / [run 44641040255](https://github.com/randogelist/Methboke/actions/runs/44641040255). [Matching evidence](../../audits/material-22431f03-accepted/summary.json). The explicit stopped premise remains unproved; full operator translation is not asserted.

## Minimal root facets

| Facet | Exact scope | Current status |
|---|---|---|
| E01.data | Literal fixed-datum canonical cutoff family | Accepted scoped helper |
| E06.scalar | Reciprocal bounds, exact scalar drift and continuity | Accepted scoped helper |
| E07.slab | Closed-slab mean-value comparison | Accepted scoped helper |
| E09.bound | Actual smooth front implies eventual canonical enstrophy bound | Accepted at 22431f03/run 44641040255 |
| E10 | Exact conditional universal-statement obstruction | Accepted at 22431f03/run 44641040255 |

The internal INT01–INT12 chain in the [cumulative B-tier text](../../EHRENFEST_OBSTRUCTION_B_TIER.txt)
and [implemented route](FAST_ROUTE.md) establishes the mathematical composition.
Its source closure has 25 owned modules and excludes hitting/escape and operator
modules not used by the literal root. The hypothetical front has T<S; the root
uses T=1/gamma and S=T+1. The eventual H1 bound is derived from actual error
calculus and the interior small-forcing comparison, not supplied as a premise.

## Evidence and counts

[IMPLEMENTATION_STATUS.json](IMPLEMENTATION_STATUS.json) retains every failed
attempt and accepted receipt. [obligations.json](obligations.json) records exact
milestone and facet gates. [COUNT_RECONCILIATION.json](COUNT_RECONCILIATION.json)
distinguishes 31 historical proposed modules, nine logical root blocks, 25
concrete root modules, 30 active owned sources and 16 Ehrenfest packages.

The active registry has 411 modules, 71 packages and 448 named audits plus QFB.
All 183 Ehrenfest declarations are accepted: 108 earlier plus 75 in the new run. No source-only or inactive PreparedE01 record adds
formal acceptance. Full original-workstream closure still requires all ten
original scopes; the stopped witness remains a separate open existence problem.

Verification is external and cached only, preserving compiler/dependency pins
and complete fresh consumer-type/axiom coverage. No local Lean, Lake or kernel
execution is permitted. WFB, R0 and QFB retain their accepted statements and
evidence as foundations; WFB's finite-budget premise is not added to this root.
