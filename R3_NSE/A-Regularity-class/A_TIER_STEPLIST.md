# NSE-A finite-charge class: B-tier step list toward A-tier

**G05 and P01–P07 are A-tier accepted at `09bcf251`**, [external run 44820225574](https://github.com/randogelist/Methboke/actions/runs/44820225574). All **496 modules, 93 fresh package audits and 987 named type/axiom reports** passed. The latest seven packages add **134 declarations: 116 theorems and 18 definitions**. Only standard axioms occur; publication and final acceptance passed. The original G05 physical H1/Fourier/six-projector scope is complete. G01, G02, G03, G04 and G06, the canonical NSE-A class root and universal budget finiteness remain open. No local Lean was executed.

M1 awaits P08; M2 and M3 retain their exact native obligations. P20 verification is satisfied for the accepted scopes. The twenty-endpoint assent remains recorded.

Repository: randogelist/Methboke. Branch: **AC-Integration**.
Source basis: **a1dea65c8eb1344b5d55157162db2d38a8d78ff3**.
The project goal remains Fefferman D; this is scoped work on the registered
whole-space regularity class.

- [Registered class](README.md)
- [Complete current B-tier derivation](NSE_A_FINITE_CHARGE_CLASS_B_TIER.txt)
- [Cumulative B-tier step-list record](NSE_A_A_TIER_STEPLIST_B_TIER.txt)
- [Machine-readable plan](A_TIER_PLAN.json)
- [Class status and evidence boundary](STATUS.json)

## Exact theorem target

For $\nu>0$ and real $a\in\mathcal S_\sigma(\mathbb R^3)$, construct its
canonical maximal $H^1$ strong solution and use

$$
\tau_A=\frac{8\|a\|_2^4}{27\pi^4\nu^5},\qquad
b_A=\min\{T_{\max},\tau_A\},\qquad
q_{\alpha,A}(t)=\|\nabla Q_\alpha U(t)\|_2^2.
$$

The canonical root target is

$$
\boxed{a\in\mathfrak C_\nu^A
\iff \int_0^{b_A}\sum_{\alpha=1}^6q_{\alpha,A}(t)^2\,dt<\infty
\iff T_{\max}(a,\nu)=\infty.}
$$

Every terminal integral is a full extended nonnegative integral, including
possible divergence at the maximal time; zero datum has zero budget.
The class remains defined by $L_A<\infty$, where

$$
J_{6,A}\le J_A\le6J_{6,A},\qquad
L_A^4=4\nu J_A=64\pi^4\nu B_A.
$$

P19 additionally identifies this canonical statement with the literal
smooth finite-energy Fefferman-A solution class. The separate universal claim
$\mathfrak C_\nu^A=\mathcal S_\sigma(\mathbb R^3)$ remains open.

## Three acceptance milestones

| Milestone | Endpoints | Exact scope |
|---|---|---|
| **M1: physical pathwise charge theorem** | P01–P08 | Six actual real-preserving Fourier projections and equivalence of the full six-charge and enstrophy budgets for a supplied physical $H^1$ path; no NSE existence/globality claim |
| **M2: canonical NSE-A class theorem** | P09–P18, using M1 | Actual local/maximal strong theory and finite-window continuation give the datumwise canonical regularity-class equivalence |
| **M3: literal class theorem and final acceptance** | P19–P20, using M2 | The literal Fefferman solution-class bridge and complete matching external type/axiom/instance verification |

P20's verification rule applies to each milestone when it is claimed accepted.
The last milestone does not defer auditing earlier accepted tranches.

The strong-solution route is sufficient: global Leray–Hopf existence,
full shifted-LH membership, weak–strong QFA comparison and the complete QFA
tail theorem are separate work, not prerequisites for this class theorem.

## The 20 contextual endpoints

Each item below specifies its output, dependency order, existing anchors,
new obligation and completion criterion. **P01–P08 / M1 are accepted; P09–P19 retain their open portions.** An accepted helper does not mark its whole parent endpoint done.

### P01. Physical H1 carrier and Schwartz admission

**Output.** Define the actual real full-volume H1_sigma carrier using L2 fields and compact-test weak derivatives. Prove gradient-witness uniqueness, the physical H1 norm/topology and completeness, and admission of real solenoidal Schwartz data.

**Dependencies.** None of the new endpoints. Independent of P02; use the closed physical weak-gradient graph.

**Existing anchors.** Native SpatialL2, SpatialWeakGradient and Solenoidal; complexifyL2LI, complexifyL2_gradientEnergy; Mathlib Lp.toTemperedDistributionCLM and ker_toTemperedDistributionCLM_eq_bot [A1-A2].

**New obligation.** Construct the closed physical weak-gradient graph as a closed subspace of the L2 product Hilbert space, prove completeness, and construct its adapters. A record of assumed global solutions is not an H1 construction. If MemSobolev 1 2 is used internally, prove agreement with the physical weak-gradient carrier.

**Complete when.** The same physical fields and norm occur in all later charge and PDE statements. The physical weak-derivative predicate and witnesses defining H1 are explicit; existence and regularity of NSE solutions are proved separately, not inserted into the H1 definition.

### P02. Two-way H1-only Fourier derivative bridge

**Output.** For v and G_j in L2, prove that G_j is the actual weak derivative of v if and only if Fourier(G_j)(xi)=2*pi*i*xi_j*Fourier(v)(xi) almost everywhere. Require first derivatives only.

**Dependencies.** P01.

**Existing anchors.** denseCompactSchwartzTests, tempered_eq_of_eq_on_compactSchwartz; native ae_eq_of_const_smul_real_multiplier_distribution; Mathlib fourier_lineDerivOp_eq and Lp.fourier_toTemperedDistribution_eq [A2-A3].

**New obligation.** Split compact complex tests into their real and imaginary parts, use the given real compact-test identities, then apply the proved density and prove the reverse multiplier-to-weak-derivative direction. The existing gradient_fourier_ae has a combined gradient/Laplacian witness type; extract a new H1-only theorem.

**Complete when.** Both directions refer to actual weak derivatives and hold without an L2 Laplacian premise. The reverse direction supports P05 without multiplying arbitrary distributions by discontinuous indicators.

### P03. Six concrete even Borel sectors

**Output.** Construct the six sectors indexed by 123,132,213,231,312,321, ordering (-|xi_j|,j) lexicographically. Prove Borel measurability, exact disjoint coverage, antipodal symmetry and nonempty interiors.

**Dependencies.** None of the new endpoints. Can be developed in parallel with P01-P02.

**Existing anchors.** Mathlib measurableSet_le, measurableSet_lt and finite measurable-set operations [A4]. The registered B-tier sector construction supplies the specification.

**New obligation.** Implement the tie rule and finite permutation proofs. The torus coordinate-zero channel partition is only a domain-specific precedent; replacing integer frequencies by continuous ones collapses its coordinate-zero sectors almost everywhere.

**Complete when.** Every frequency, including ties and the origin, belongs to exactly one prescribed sector; the definition is fixed independently of datum, viscosity and time.

### P04. Actual L2 Fourier projections and real preservation

**Output.** Construct Q_alpha = Fourier inverse composed with multiplication by the sector indicator composed with Fourier. Prove bounded linearity, norm contraction, idempotence, self-adjointness, pairwise orthogonality, sum Q_alpha=I and preservation of real fields.

**Dependencies.** P01,P03. Use the actual L2 Fourier transform; P02 is not needed to construct the L2 operator.

**Existing anchors.** Mathlib MemLp.indicator, eLpNorm_indicator_le, MemLp.toLp, Lp.ext, Lp.fourierTransformₗᵢ, norm_fourier_eq and inner_fourier_eq; Complex.conjLIE and Lp.compMeasurePreserving support the reality bridge [A5].

**New obligation.** Build the operator directly on L2 and prove its real range through Fourier conjugation/reflection. Do not use the smooth tempered-distribution multiplier constructor for discontinuous cones. indicatorConstLp requires finite measure and is unsuitable for the infinite-volume cones.

**Complete when.** The projections exist as operators on the actual physical L2 carrier and preserve conjugate symmetry; boundedness of a formal symbol alone does not complete the endpoint.

### P05. H1 derivative commutation and solenoidal preservation

**Output.** Prove SpatialWeakGradient(v,G) implies SpatialWeakGradient(Q_alpha v, j maps to Q_alpha G_j), prove H1 contraction, and prove Solenoidal(v) implies Solenoidal(Q_alpha v).

**Dependencies.** P02,P04.

**Existing anchors.** P02 both ways and P04 actual L2 indicators; the accepted wholeSpaceSpectralEndpoint is a normalization/reference anchor with its own combined witness premises [A3,A6].

**New obligation.** Use almost-everywhere multiplier multiplication inside L2 and return to physical weak derivatives using P02. Do not impose H2 or Schwartz membership merely to fit an existing theorem.

**Complete when.** The theorem applies to every physical H1 input. Sharp sector projections need not preserve Schwartz fields and their outputs are not asserted to be independent NSE solutions.

### P06. Enstrophy additivity and exact Fourier factors

**Output.** Define q_alpha as the sum of the three projected gradient L2 norm squares. Identify it with ||grad Q_alpha v||_2^2 and with 4*pi^2 integral_(C_alpha) |xi|^2 |Fourier(v)|^2. Prove sum_alpha q_alpha = Y = ||grad v||_2^2.

**Dependencies.** P02,P05.

**Existing anchors.** QFA.LC001SpectralReduction.integrable_norm_sq, integral_norm_sq_eq_norm_sq, integrable_gradient_fourier_sum, integral_gradient_fourier_sum; complexifyL2_gradientEnergy; Mathlib memLp_two_iff_integrable_sq_norm [A1,A6].

**New obligation.** Assemble the six disjoint indicator integrals with all vector components and the Frobenius gradient norm. Prove gradient-witness independence from P01.

**Complete when.** Every equality is for the same actual field, and every required real spatial integral is genuinely integrable before a Bochner integral is used.

### P07. Factor-six comparison for nonnegative charges

**Output.** For six nonnegative charges prove sum q_alpha^2 <= (sum q_alpha)^2 <= 6 sum q_alpha^2, then specialize to the actual enstrophy Y.

**Dependencies.** P06. The generic scalar lemma can be proved independently; this dependency is for its physical specialization.

**Existing anchors.** Mathlib Finset.sum_sq_le_sq_sum_of_nonneg and Finset.sum_mul_sq_le_sq_mul_sq [A7].

**New obligation.** Prove the Fin 6 specialization and preserve the nonnegativity hypotheses. This is a comparison, not an equality of the two squared-charge quantities.

**Complete when.** The physical inequality is sum q_alpha^2 <= Y^2 <= 6 sum q_alpha^2. No global regularity or finite-budget hypothesis is used.

### P08. Extended budgets, endpoint limits and gauge normalization

**Output.** For a supplied physical H1 path and finite horizon define ENNReal nonnegative lintegral budgets J_A,J_6,A,B_A. Prove J_6,A<=J_A<=6 J_6,A, all finiteness equivalences, the complete increasing improper-limit identity, L_A^4=4*nu*J_A=64*pi^4*nu*B_A, zero-window formulas and sublevel exhaustion.

**Dependencies.** P01,P07. Retain exact measurability hypotheses for a generic path.

**Existing anchors.** Mathlib lintegral_mono, lintegral_mono_ae, lintegral_finsetSum', lintegral_const_mul', lintegral_iSup', lintegral_tendsto_of_tendsto_of_monotone, lintegral_ofReal_ne_top_iff_integrable, ofReal_integral_eq_lintegral_ofReal; ENNReal.rpow_mul, rpow_natCast, rpow_lt_top_iff_of_pos [A8].

**New obligation.** Retain infinity until finiteness is proved. For a maximal lifetime take the minimum with the finite cutoff before converting to a real endpoint, or use the set {0<t, ofReal(t)<T_max, t<tau_A}. Derive path measurability from actual H1 continuity at instantiation.

**Complete when.** Divergent budgets remain infinity; no totalized real integral or premature toReal can turn divergence into zero. This milestone is pathwise, before canonical datum-class construction.

### P09. Whole-space spatial estimates and sharp cutoff admission

**Output.** Prove the required physical Sobolev/interpolation inequalities, vector/tensor norm extensions and ||D^2 v||_2=||Delta v||_2. Prove admissibility of S_6=2^(2/3)/(sqrt(3)*pi^(2/3)), hence S_6^6=16/(27*pi^4).

**Dependencies.** P01,P02. Also construct the physical H2 derivative adapter.

**Existing anchors.** Mathlib MeasureTheory.eLpNorm_le_eLpNorm_fderiv_of_eq_inner; accepted distributional multipliers/wholeSpaceSpectralEndpoint; the Talenti primary theorem [A3,A6,A9,L1].

**New obligation.** Extend compact-C1 estimates to the same physical H1 space and prove all norm identifications. The inspected Mathlib Sobolev constant is not the registered sharp value. A proved arbitrary admissible S is a useful intermediate, but numerical specialization is separate.

**Complete when.** The spatial inequality itself justifies the constant used by tau_A. A scalar sixth-power identity, an extremal calculation or a cited literature theorem without formal proof does not close the numeric endpoint.

### P10. Actual norm-controlled local H1 NSE construction

**Output.** Build the whole-space heat and Leray operators, prove the Duhamel bilinear estimates in an actual solution space, construct the fixed point for every H1_sigma datum, and prove uniqueness, C_t H1 / L_t^2 H2 regularity and a positive lifespan controlled only by nu and the H1 bound. Construct the zero solution.

**Dependencies.** P01,P09. Required heat/Leray analysis is part of the new obligation.

**Existing anchors.** Periodic uniform_H1_local_initial_classical_front_exists is a construction model; Tao Theorem 5.4 supplies the analytic target. Upstream StrongSolutionOnIcc is only a supplied-H3-solution contract [A10,L2].

**New obligation.** Prove the R3 IVP constructor and quantitative lifespan. A record of a supplied H3 solution, comparison of two supplied solutions, or a theorem assuming compact spatial support does not construct this solution. Do not assume compact-support or Schwartz preservation at restarts.

**Complete when.** There is an inhabited physical local solution for every actual H1 restart datum, with the uniform lifespan needed by P11. No unconstructed local-solution or fixed-point witness remains in the final constructor.

### P11. Canonical maximal development and H1 continuation

**Output.** Glue the uniquely compatible local developments, define T_max in (0,infinity], construct the canonical trajectory, prove overlap uniqueness, and prove that a uniform H1 bound excludes a finite terminal lifespan.

**Dependencies.** P10.

**Existing anchors.** Periodic maximal_classical_front_exists_of_local_existence and maximal_classical_lifetime_eq_top_of_uniform_H1 are proof patterns; Tao Theorem 5.4 and Corollary 5.8 give the whole-space analytic target [A10,L2].

**New obligation.** Supply every R3 existence/uniqueness instance. Restart near a hypothetical finite endpoint using the norm-controlled local lifespan; do not assume a strong H1 trace at that endpoint.

**Complete when.** The canonical path exists for every datum before the budget class is instantiated. Bounded H1 continuation is proved for this same path and actual PDE, including the zero-data branch.

### P12. Finite-front energy and weighted product

**Output.** Derive the strong energy identity E(t)+2*nu integral_0^t Y=E_0 on every compact strong slab. Prove energy monotonicity and integral_0^R E*Y=(E_0^2-E(R)^2)/(4*nu)<=E_0^2/(4*nu) for every 0<=R<T_max.

**Dependencies.** P10,P11.

**Existing anchors.** Accepted QFA.Energy.product_budget_Ioo is a domain-neutral finite-interval scalar anchor. Native LerayHopf.energy_product_budget_Ioo is a GLOBAL-LH wrapper with stronger input [A11].

**New obligation.** Derive the energy data from the actual finite strong PDE front, then feed the scalar lemma. Do not assume global LH membership to apply the native wrapper while global strong continuation is still being proved.

**Complete when.** All temporal/spatial integrability and cancellation premises are discharged on a finite front. No global PDE solution has been smuggled into the weighted-budget proof.

### P13. Actual enstrophy evolution and nonlinear estimates

**Output.** On every finite closed interval [0,R] with 0<=R<T_max, prove absolute continuity of Y and the justified chain rule from the strong PDE. Derive Y'+nu*Z <= pi^(-4)*nu^(-3)*Y^3 almost everywhere and |N|<=S_6^(3/2)*(E*Y)^(1/4)*Z, with Z=||Delta U||_2^2.

**Dependencies.** P09,P12.

**Existing anchors.** Periodic INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC is a physical proof pattern. Recovered scalar absorption is algebra only. The scalar CubicBudget module is compiled, but CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL is not a directly named audit root in the retained run [A12].

**New obligation.** Establish the whole-space cancellation, integration by parts, actual time derivative/absolute continuity and estimates. Prefer an AC formulation suitable for H1 theory; do not depend on the later literal smooth-pressure bridge merely to justify this stage.

**Complete when.** The differential inequality is derived for actual trajectories, rather than supplied as a record field. Its pi factor follows from P09's admissible S_6 and the scalar Young inequality.

### P14. Small-product global H1 restart

**Output.** For an actual H1 trace U(s), prove E(s)*Y(s)<nu^4/S_6^6 gives a fixed positive dissipation margin, invariant bounded enstrophy and global strong continuation from that trace.

**Dependencies.** P11,P13.

**Existing anchors.** The registered B-tier small-product proof and recovered ScalarProfile.enstrophy_absorption provide the scalar pattern [A12].

**New obligation.** Prove the first-exit/continuity bootstrap over time, use energy monotonicity, and apply actual bounded-H1 continuation. A pointwise absorption inequality alone does not establish the invariant or a global solution.

**Complete when.** The restart theorem accepts arbitrary H1_sigma traces and extends the actual solution with a strictly positive margin; it does not assume the trace is Schwartz or H3.

### P15. Full budget implies strict cutoff crossing

**Output.** Use the cubic inequality and finite complete J_A to bound Y by Y(0)*exp(pi^(-4)*nu^(-3)*J_A). Combine with E(t)<=E_0 and continuation to prove T_max>tau_A, excluding equality.

**Dependencies.** P08,P11,P13.

**Existing anchors.** Compiled CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL supplies a scalar pattern only after its continuity/derivative premises are met; prove an AC variant if using rough H1 regularity. Periodic physical budget continuation supplies a model [A10,A12].

**New obligation.** Pass from the full ENNReal endpoint budget to the required finite integrals and uniform bound. The periodic proof's Poincare step must be replaced by the independent energy bound E<=E_0 on R3.

**Complete when.** The contradiction covers T_max<=tau_A, including equality, without presuming U(T_max) exists. Finiteness on each smaller interval is never substituted for the full budget.

### P16. Strict interior good time at the registered cutoff

**Output.** For nonzero a and the strong solution now existing beyond tau_A, select 0<s<tau_A with E(s)*Y(s)<nu^4/S_6^6. Retain the half-window estimate if packaged.

**Dependencies.** P09,P12,P15.

**Existing anchors.** Accepted exists_good_time_of_product_budget, exists_good_time_of_energy_envelope, good_set_measure_ge_half_of_product_budget and safeCutoff_eq_pi_formula_of_sixth_power [A13].

**New obligation.** Instantiate M=||a||_2 and Good=True on the strong front, supply P12's actual energy envelope/product budget, and use P09 for physical Sobolev admissibility. No global LH restart predicate is needed.

**Complete when.** The selected trace is actual H1 data strictly inside the available strong interval. The exact numerical tau_A follows from an admitted spatial estimate, not arithmetic alone.

### P17. WFA forward implication for the same trajectory

**Output.** Compose cutoff crossing, the good trace and global small-product restart. Use strong overlap uniqueness and maximality to prove finite J_A implies T_max=infinity for the original canonical trajectory.

**Dependencies.** P11,P14,P15,P16.

**Existing anchors.** Existing B-tier E08-E10 supplies the exact argument. Periodic same-front continuation/gluing is a domain-specific model [A10,B1].

**New obligation.** Prove the restarted path agrees with U on their common time interval and produces a genuine extension. Do not replace U with an unrelated weak or smooth solution.

**Complete when.** The forward theorem retains the finite full budget hypothesis and discharges all physical existence, continuation, overlap and restart premises. It does not claim that every datum has a finite budget.

### P18. Canonical regularity-class equivalence

**Output.** Instantiate the class with the constructed canonical solution and prove a in C^A_nu iff J_6,A<infinity iff T_max=infinity. Prove the reverse using H1 continuity on [0,tau_A], plus zero data, gauge normalization and sublevel exhaustion.

**Dependencies.** P08,P11,P17.

**Existing anchors.** P08's physical pathwise characterization; the registered class theorem and its compact-interval converse [B1-B2].

**New obligation.** Define canonical selection only from P11's proved existence/uniqueness. Keep the class definition based on finite charge, not on globality itself; then prove the equality of those independently defined predicates.

**Complete when.** The final canonical datum-class theorem has only the intended viscosity/data assumptions, with no unconstructed maximal-solution port, universal-budget premise or assumed regularity iff as an extra field.

### P19. Literal Fefferman-A solution-class identification

**Output.** For Schwartz data prove velocity/normalized-pressure smoothness on [0,R] whenever 0<=R<T_max, including time zero; hence on every finite slab for class members with T_max=infinity. Derive their global energy bound. Prove the A4 converse identifying any literal smooth finite-energy Fefferman pair with the canonical H1 development on finite slabs.

**Dependencies.** P10,P11,P18. Add the physical smoothing/pressure and closed-slab identification arguments.

**Existing anchors.** Tao Theorem 5.4, Corollaries 4.3,5.8,11.1 and the literal Fefferman problem statement are analytic specifications, not already imported Lean proofs [L2-L3].

**New obligation.** Formalize pressure recovery, all required spatial/time regularity, bounded-enstrophy and normalized-mild identification, and strong uniqueness. A4 cannot remain an unproved theorem parameter in a claimed literal Fefferman-A class equivalence.

**Complete when.** The forward output and converse competitor have exactly the literal smooth finite-energy category. Equality of pressure gradients precedes the smooth time-gauge conclusion. No universal regularity result is inferred.

### P20. Exact cached external acceptance and publication

**Output.** For each tranche and the final root, obtain matching external compilation, independent expected-type/literal-contract consumers, named theorem-level axiom reports, exact source/dependency/policy identities and successful publication/final acceptance.

**Dependencies.** P08,P18,P19. These final dependency heads cover P01-P19 transitively; the same gate also applies whenever an earlier tranche is accepted.

**Existing anchors.** Existing Material cached external workflow and retained afd67db4/run44788963412 evidence conventions [E1].

**New obligation.** Add every new declaration to its package/index/audit coverage; inspect the final theorem parameters and all analytic instances. The previously compiled scalar cubic helper needs a named report if claimed as a directly accepted new endpoint. Preserve pins and existing audits.

**Complete when.** No sorryAx or unapproved axiom; no hidden local-existence/Sobolev/continuation/global-reference premise; exact tested proof bytes and full intended types match. A successful helper audit never promotes its parent root. Local Lean/Lake/kernel execution remains absent.

## Dependency order and noncircularity

P01–P08 form the physical spectral/budget layer. P03 and the scalar part of
P07 can be developed independently. P09 supplies spatial estimates; P10–P11
construct the actual local/maximal evolution. P12–P13 derive its balances.
P14 is the small-product route, while P15 crosses the finite front window.
P16 then selects an available interior trace, P17 extends the same path, and
P18 proves the class identity. P19 adds the literal solution category.

The finite-window scalar identities are

$$
E'= -2\nu Y,\qquad
\int_0^R EY\,dt=\frac{E_0^2-E(R)^2}{4\nu},\qquad
Y'+\nu Z\le\pi^{-4}\nu^{-3}Y^3.
$$

With $\theta=\nu^4/S_6^6$ and
$\tau_A=S_6^6E_0^2/(2\nu^5)$, the product bound uses only half the
threshold-length product. After P15 establishes $T_{\max}>\tau_A$, the
accepted scalar selector gives a restart strictly before the cutoff.
No value at a potentially terminal $T_{\max}$ is presumed.

The complete initial $H^1$ theory must be constructed before canonical
selection is used in the final class definition. Neither an assumed
maximal-solution port nor a definition equating membership with globality
can replace that proof.

### First formal obstruction

P08: construct the ENNReal lifetime/finite-cutoff adapter, exact observation set, full partial-budget supremum and gauge/sublevel interface for supplied actual H1 paths.

The physical H1/Fourier/six-projector chain P01–P07 is accepted. The later
independent native requirements remain actual R3 local/maximal H1 NSE, sharp
spatial admission, physical balances/continuation and the literal class bridge.

For this conditional class theorem, the open universal budget assertion is
not an input to discharge. The separate universal-regularity edge remains

$$
\text{energy and }\int EY\text{ bounds}
\quad\Longrightarrow\quad
\forall a\in\mathcal S_\sigma,\ J_A(a,\nu)<\infty,
$$

and has not been proved. The proposed plan proves the equivalence with a
finite budget; it does not assert that every datum satisfies that condition.

## Source and evidence register

**E1 — Existing acceptance.** Native/recovered QFA foundations at
[afd67db4](https://github.com/randogelist/Methboke/commit/afd67db40e71bd1412c82247a78598288deb611e),
[external run 44788963412](https://github.com/randogelist/Methboke/actions/runs/44788963412).
See [the exact integration record](../QFA/INTEGRATION_STATUS.json) and
[accepted declaration register](../QFA/QFA_FOUNDATIONS_A_TIER.txt).
They do not certify these 20 proposed endpoints.

**Pinned environments.** Material uses Lean 4.33.0 and Mathlib
**db584cd6d46c92f209a44c0f1c829460d327499d**. The recovered QFA source is
Methlib **53b2318c2b586137b6db74c4d3a41bb0b964b2d8**. Mathlib declarations
below are inspected source anchors at that pin; each new adapter still needs
its own exact external evidence. The upstream H3 snapshot uses a different
4.34.0-rc2 environment and has no automatic native compatibility.

| Ref | Verified anchor locations and scope |
|---|---|
| **A1** | Material/MethbokeAddon/QuasiFeffermanA/Contracts.lean; Material/_vendor/QFA/Endpoints/Representation/Complexification.lean. Actual full-volume carriers, compact real test predicates and real/complex isometries. |
| **A2** | Material/_vendor/QFALC004/CompactSchwartz.lean; Material/_vendor/QFALC005/Density.lean; Mathlib/Analysis/Distribution/TemperedDistribution.lean. Compact-test density and injectivity; native physical H1 instantiation remains new. |
| **A3** | Material/MethbokeAddon/QuasiFeffermanA/FourierMultipliers.lean; Mathlib/Analysis/Distribution/TemperedDistribution.lean and Analysis/Fourier/LpSpace.lean. Polynomial distribution multipliers; existing public gradient helper has an extra Laplacian-witness interface. |
| **A4** | Mathlib/MeasureTheory/Constructions/BorelSpace/Order.lean. Measurability of inequalities used in the fixed sector definition. |
| **A5** | Mathlib/MeasureTheory/Function/LpSeminorm/Indicator.lean; Function/LpSpace/Basic.lean; Analysis/Fourier/LpSpace.lean; Analysis/Complex/Basic.lean; Integral/Bochner/ContinuousLinearMap.lean. Direct L2 indicators, Fourier isometry and conjugation/reflection tools. |
| **A6** | Material/_vendor/QFALC001Reduction/NativeFromAENorms.lean; Material/MethbokeAddon/QuasiFeffermanA/Spectral.lean; Mathlib/MeasureTheory/Function/L2Space.lean. Norm-integral helpers and accepted combined-witness spectral endpoint. |
| **A7** | Mathlib/Algebra/Order/BigOperators/Ring/Finset.lean. Finite nonnegative-sum and Cauchy–Schwarz inequalities. |
| **A8** | Mathlib/MeasureTheory/Integral/Lebesgue/Basic.lean and Add.lean; Function/L1Space/Integrable.lean; Integral/Bochner/Basic.lean; Analysis/SpecialFunctions/Pow/NNReal.lean. ENNReal integration, increasing limits, finite real-integral conversion and positive fractional powers. |
| **A9** | Mathlib/Analysis/FunctionalSpaces/SobolevInequality.lean. Genuine compact-C1 Sobolev inequality with a different constant; physical H1 and sharp-constant admission remain separate. |
| **A10** | Material/MethbokeAddon/WeakFouriermanB/{LocalExistence,MaximalClassicalFront,StrongContinuation,PhysicalEndpointContinuation,PhysicalBudgetContinuation}.lean. Accepted periodic construction patterns; R3 instances remain new. |
| **A11** | Material/_vendor/QFA/Endpoints/Energy/ProductBudget.lean, especially QFA.Energy.product_budget_Ioo; native Energy.lean's LH wrapper. The scalar anchor is finite-interval and domain-neutral; the native wrapper assumes a global LH record. |
| **A12** | Material/MethbokeAddon/WeakFouriermanB/PhysicalEnstrophyEvolution.lean; Material/_vendor/SingularClosure/CubicBudget.lean; Material/_vendor/QFA/Endpoints/Agmon/Scalar.lean. Physical periodic and scalar patterns with explicit premises. |
| **A13** | Material/MethbokeAddon/QuasiFeffermanA/Cutoff.lean. Accepted scalar selector, half-measure and cutoff arithmetic; physical Sobolev admissibility is not a conclusion of those helpers. |

**Cubic-helper qualification.**
SingularClosure.CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL has a compiled
source module in the accepted run but is not a directly named audit root in
that report. Its type asks for continuous y,z,d on a closed interval,
a pointwise derivative of y in the interior, the cubic inequality and a
square budget. For rough H1 evolution, an AC form is the preferred route;
otherwise all stronger continuity/derivative premises must be proved.
It does not establish the physical enstrophy identity.

**Multiplier qualification.**
TemperedDistribution.MemSobolev.fourierMultiplierCLM_of_bounded also requires
HasTemperateGrowth. Boundedness alone does not make discontinuous cone
indicators eligible. P04 uses MemLp.indicator/toLp directly on L2.

**B1 — Existing analytic chain.**
[Whole-space cumulative specification](../../Temp-folder/specification/FEFFERMAN_A_ELEMENTWISE_FINITE_WINDOW_B_TIER_v0_1.txt),
A0–A4, E01–E10 and Sections 13–15.

**B2 — Registered class.**
[NSE_A_FINITE_CHARGE_CLASS_B_TIER.txt](NSE_A_FINITE_CHARGE_CLASS_B_TIER.txt),
especially the sector construction, full endpoint, globality proof and A4 boundary.

**L1 — Talenti.** Giorgio Talenti, “Best constant in Sobolev inequality”,
Annali di Matematica Pura ed Applicata 110 (1976), 353–372; opening theorem
and formula (2), dimension 3 and exponent 2.
[Primary text](https://math.jhu.edu/~js/Math646/talenti.sobolev.pdf).

**L2 — Tao.** Terence Tao, “Localisation and compactness properties of the
Navier–Stokes global regularity problem”, Analysis & PDE 6(1) (2013), 25–107.
Theorem 5.4 and Corollary 5.8 give the H1 local/continuation specification;
Corollaries 4.3 and 11.1 give the normalized-mild and bounded-enstrophy
identification used for A4.
[Primary text](https://msp.org/apde/2013/6-1/apde-v6-n1-p02-s.pdf).

**L3 — Fefferman.** The literal whole-space target is statement (A), with
data condition (4) and output conditions (6)–(7), in the
[official problem statement](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf).
These literature references are mathematical sources, not imported Lean proofs.

## Prospective source organization

The following is a proposal only; these files/packages are **not created by
this step-list update**. A separate owned namespace can keep the accepted
QFA sources intact:

| Prospective owned modules under Material/MethbokeAddon/NSEAFiniteCharge/ | Planned endpoints |
|---|---|
| Spaces, SpatialBridge, Sectors, Projectors, ChargeIdentities, Budgets | P01–P08 |
| SpatialEstimates, LocalStrong, MaximalStrong, StrongEnergy, Enstrophy | P09–P13 |
| SmallProduct, WindowContinuation, ClassEquivalence | P14–P18 |
| FeffermanBridge | P19 |

Prospective package names are NSEAFiniteChargeSpectral,
NSEAFiniteChargeContinuation and NSEAFiniteChargeRoot, each with explicit
Endpoint/Audit files when authorized. Package/index entries must be added
only alongside actual prepared sources and checked for complete coverage.

## Assent and acceptance boundary

This is the concrete 20-endpoint proposal for user review. After assent,
bottom-up preparation may begin with M1, while scalar P07/P08 helpers can be
separated into smaller exact scopes. New sources remain pending until their
matching external evidence passes P20. No part of this plan grants itself
A-tier status or closes a physical root from a helper's audit.

No local Lean, Lake, kernel audit or project runner was executed. This update
creates no Lean declaration and starts no compiler/audit run. It preserves
existing proof bytes, accepted evidence, dependency/compiler identities and
the Fefferman-D project goal.

## Attained Lean cutouts and revised gap assessment

The [source collection](LEAN_CUTOUTS/README.md) now contains 51 exact cutout
blocks and 60 full source snapshots, with pinned provenance and proof limits.
[The six-gap assessment](LEAN_CUTOUTS/GAPS.md) ranks the substantive missing
native constructions and distinguishes them from available lower lemmas.

P15 has a stronger reuse route: [ES02](LEAN_CUTOUTS/cards/ES02.md) supplies
AC FTC, and the already audited [ES03](LEAN_CUTOUTS/cards/ES03.md) supplies
integral Gronwall after the actual PDE-to-Volterra inequality is derived.
The new spectral, multiplier and convection source narrows P01-P05/P12-P13,
while the sharp constant, actual H1 local/maximal theory and literal A4
terminal control remain explicit. All plan endpoints retain their proposed
status. Addendum 1.1 of the cumulative step-list TXT gives every cutout path.


## Authorized six-gap construction

The [six parent targets](SIX_GAP_A_TIER_TARGETS.txt) group the unchanged twenty
endpoints. G05 is accepted; G01,G02,G03,G04,G06 remain open. The
[implementation register](SIX_GAP_IMPLEMENTATION_STATUS.json) records the exact
accepted scopes and historical attempts. The cumulative TXT retains every
prior derivation and the later H2/full-window chains.

## P08 / M1 acceptance update, 21 November 2026

The exact supplied-path P08 endpoint is accepted at `d403c235`,
[run44837033211](https://github.com/randogelist/Methboke/actions/runs/44837033211).
The full stopped-window/gauge and improper-limit clauses are covered by
`QFAStoppedBudget` and `QFAPhysicalStoppedGauge`, using accepted physical
H1 sectors. [Clause review](../../audits/material-d403c235-nse-a-accepted/semantic-review.json).
M1 is complete; M2/M3 and the five general PDE parent targets remain open.
