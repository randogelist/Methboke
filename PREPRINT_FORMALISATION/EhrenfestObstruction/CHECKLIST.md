# EHRENFEST-OBSTRUCTION: ten mid-tier steps

The [cumulative B-tier derivation](../../EHRENFEST_OBSTRUCTION_B_TIER.txt) contains all ten mathematical derivations. **E08 and E10 consume the explicit stopped-bound premise**; E01–E07 and E09 establish the underlying analytic constructions and implications. Cutoffs satisfy `N ≥ 1`. The boxes below record future external formal acceptance; none is checked by mathematical exposition or source review.

**Root:** `StoppedCommutatorBound ν → ¬ NSE_B ν`, for `ν > 0`. The premise is an explicit argument, not a global custom axiom. Its existence for a fixed smooth datum remains open.

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

- [ ] **E07 — STOPPED_SCALAR_HITTING_BOUND**
  For 0<r<v(0)<=1 and gamma>0, pre-hit drift v prime<=-gamma up to 1/gamma forces a hit of r by (v(0)-r)/gamma<1/gamma.
  B-tier: derived. Sources: ML13. New formal work: Continuity and pre-hit guard, finite/empty hitting-set cases, derivative comparison without assuming a hit already exists.

- [ ] **E08 — CUTOFF_UNIFORM_THRESHOLD_ESCAPE**
  From the explicit StoppedCommutatorBound premise for one fixed smooth datum, derive t_N<1/gamma with e_N(u_N(t_N))>=R_N and hence divergent slab suprema.
  B-tier: derived. Sources: ML13, MLB10, MLB12. New formal work: Keep a, gamma and e_* independent of N, R_N tending to infinity, and the first-hit stopping rule.

- [ ] **E09 — SMOOTH_FRONT_GALERKIN_STABILITY**
  An actual smooth solution U on [0,T] implies exact P_Na Galerkin convergence in C([0,T];H2) and uniform H1 there.
  B-tier: derived. Sources: ML03, ML08, MLB11, MLB14, MLB17, MLB19, MLB20. New formal work: New H2 residual/error estimate and first-exit Gronwall bootstrap. Existing conditional H2-budget and local bounds do not supply this full-slab implication.

- [ ] **E10 — EHRENFEST_OBSTRUCTION**
  For nu>0, StoppedCommutatorBound nu implies not NSE_B nu; its fixed smooth datum has no smooth continuation through 1/gamma.
  B-tier: derived. Sources: MLB15, MLB16. New formal work: Literal universal-global-smooth statement and existential counterexample semantics; explicit premise argument; exact endpoint and standard-axiom audit.

## Evidence and execution

The [source index](ANCHOR_INDEX.md) has 47 exact anchors: 27 pinned Mathlib source references, 13 source-reviewed declarations in accepted Methlib modules, and 7 declarations with named external type/axiom audits. These statuses belong to the listed anchors, not the ten new endpoints.

The proposed schedule starts with literal data/reciprocal interfaces and independent E07, while E09 and the phase-space adapter proceed in parallel. E04 (unbounded generator/core) and E09 (full-slab Galerkin stability) are substantial new work. No suitable already accepted Stone/core endpoint has been located.

Later acceptance requires the matching external cached compiler, exact endpoint type and theorem-level axiom audit. No local Lean, Lake or kernel execution is permitted. This documentation-only update dispatches no verification run.

Machine ledger: [obligations.json](obligations.json). Exact pinned signatures: [ANCHOR_INDEX_v0_2.json](ANCHOR_INDEX_v0_2.json).

## Refined module and acceptance map

[LEAN_LAYOUT.md](LEAN_LAYOUT.md) proposes 26 owned modules and ten full milestone packages. [MODULE_PLAN.json](MODULE_PLAN.json) records the exact planned own-import DAG; [INTERFACES.lean.txt](INTERFACES.lean.txt) gives eight uncompiled signatures. No new Lean source is activated.

E06 splits into an early scalar identity and its later full operator interpretation. E08 uses only the scalar part plus E07. E09 uses the existing forward canonical family, not E02's new complete-flow construction. The dynamical E10 implication can therefore be audited before E03–E06 are complete. The full workstream requires separate acceptance of the actual Heisenberg translation and canonical rate equality. Passing a helper never checks its enclosing box.

For the front-based E09 interface require `T<S`, since `InitialClassicalFront` at `S` has an open terminal edge. A global solution supplies `S=T+1`. The stronger actual closed-slab statement remains separately scoped.
