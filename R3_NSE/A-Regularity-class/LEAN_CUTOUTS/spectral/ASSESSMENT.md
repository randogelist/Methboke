# P01–P08: spectral source collection and remaining Lean work

**Status: static reference collection; no new A-tier acceptance.** This collection contains **21 exact declaration slices and 35 complete original source modules**. SP01–SP16 preserve the pinned native/Mathlib baseline; SP17–SP21 add five substantive source candidates from the newly attained Leray–Hopf repository. Additional full modules preserve the representations, imports and proof context needed to assess those candidates. The cutouts are `.lean.txt` reference files, not independently compiled modules or a closed dependency package.

The repository basis is `randogelist/Methboke` at `ce7f809ad20b3498a63420a22d17b3c801dfd558`, on `AC-Integration`. The plan and the Fefferman-D project goal are unchanged. [catalog.json](catalog.json) records every exact commit, original path, inclusive source range, SHA256, import, selected declaration, hypothesis boundary and evidence classification.

## Main findings

### 1. P01 has more direct infrastructure than the earlier register displayed

SP03 retains the root theorem `ae_eq_of_integral_contDiff_smul_eq`, which separates locally integrable vector fields using **real smooth compactly supported scalar tests**. It fits uniqueness of native weak-gradient witnesses: two witnesses for the same field give equal test pairings, and their L2 membership supplies local integrability. This avoids making gradient uniqueness depend on the later Fourier theorem.

SP02 retains `ContinuousLinearMap.isClosed_eqLocus`, `isComplete_eqLocus` and `completeSpace_eqLocus`, as well as their kernel versions. Once the physical weak-gradient graph is represented using continuous test/distribution maps, the general closed-equalizer completeness argument is already available. The maps, equality with the native compact-test relation, physical H1 norm and solenoidal closure still require an owned proof. No complete physical H1 carrier is created by copying these statements.

The accepted native full-volume carriers and predicates are in SP01. SPS16 retains the actual real-to-complex L2 isometry, gradient norm identity, and compact-test transport. The new external `LerayHopf.H1Sigma_R3` in SPS33 is useful as a membership model, but is a submodule of ambient L2. It does **not**, by that definition, supply the complete H1 graph-norm structure required in P01. SPS29 records its componentwise `MemSobolev 1 2` predicate; SPS30–SPS31 expose the actual carriers and Schwartz divergence tests.

### 2. There is a substantive external spectral-H1 route, but native identification is unfinished

SP17 constructs scalar complex L2 directional-derivative representatives from componentwise `MemSobolev 1 2`. It proves the exact tempered-distribution derivative identity and real-Schwartz integration by parts. SP18 constructs the weighted Fourier L2 representatives and their norm formulas. SP21 proves the reverse **spectral-membership** direction: finite actual componentwise weighted Fourier lintegrals imply `memH1VF_R3`.

These are proof bodies, not merely fields of a proposed PDE record. SPS32 preserves the forward weighted-integrability proof, including the extraction of the a.e. Bessel-multiplier identity from an L2 distribution equality. Some adjacent historical comments still call that edge open; the selected conclusion is based on the actual body present at the pinned commit, with no compiler claim inferred from comments.

The remaining P02/P05 work is precise: identify this componentwise spectral predicate with the native real-vector compact-test H1 carrier; prove the physical first-derivative Fourier identity in both directions; assemble scalar component derivatives into the actual real-vector gradient; and use the result for sharp-mask commutation and solenoidal preservation. The native accepted SP05 gradient wrappers still take a combined first-derivative/Laplacian witness record. The required new H1 theorem must not acquire an L2-Laplacian premise merely to fit that interface.

SP04 proves compact complex Schwartz test density. It does not itself convert native real compact tests into complex Schwartz identities. That conversion splits a complex test into its real and imaginary parts, applies the actual real-test identities, and then uses density. SPS15 provides the continuous/injective L2 distribution embedding and the forward/inverse Fourier derivative identities.

### 3. The bounded measurable mask construction now has a close external model

SP19, `LerayHopf.BoundedMultiplier`, constructs multiplication by an essentially bounded measurable **real symbol** on actual scalar complex L2. It proves the representative equation, real linearity, norm bounds, continuity and self-adjoint pairing. It assumes no smoothness or `HasTemperateGrowth` of the symbol. Consequently it is a suitable source model for measurable cone indicators after instantiation and vector adaptation.

The pinned Mathlib alternative remains SP07 with `MemLp.indicator`, `eLpNorm_indicator_le`, and the `MemLp.toLp`/`Lp.ext` declarations preserved in SPS08. The cone itself need not have finite volume. The unrelated `indicatorConstLp` constructor requires finite measure and is not the intended route.

The six fixed even sectors, indicator algebra, idempotence, mutual orthogonality, identity reconstruction and H1 commutation remain to be proved for the registered operators. Neither SP19 nor the Mathlib lower tools already implements that family. The `MemSobolev.fourierMultiplierCLM_of_bounded` theorem in SPS18 also requires `HasTemperateGrowth`; it cannot be applied to discontinuous sharp sector indicators.

### 4. Real preservation has an actual L2 proof template

SP20 retains an existing scalar **L2** Hermitian-reflection proof, not just a Schwartz-level assertion. It extends real-Schwartz conjugate symmetry by density and continuity, using actual L2 reflection and conjugation maps. SP08 supplies the pinned domain-composition isometry; SP09 supplies semilinear codomain lifting to Lp.

Both SP20 names, `reflect_fourier_schwartzC_eq_conj` and `fourier_ofReal_reflect_eq_conj`, are **private source declarations**. Their spellings identify the retained proof bodies; they are not public names that a consumer can import and call. An owned public proof still needs preparation and matching verification. Its reverse/inverse real-range implication, Euclidean-vector assembly, compatibility with the native complexification, and preservation under even masks remain explicit obligations. SPS27 also preserves public Schwartz Hermitian/preimage arguments as further context; a Schwartz-only theorem cannot be applied directly to the discontinuously projected field.

### 5. Charge algebra and extended-budget machinery are comparatively well supported

SP10 gives accepted actual-L2 squared-norm integrability and finite-gradient-sum identities. Its four selected statements do not require a Laplacian or derivative record. P06 still has to connect those identities to the same physical gradient and six projections, including every vector component and the factor `4*pi^2`.

SP11 supplies both finite-sum inequalities needed for `sum q_alpha^2 <= Y^2 <= 6*sum q_alpha^2`. This is a short scalar specialization after P06, not a new regularity estimate.

SP12–SP16 preserve monotone convergence, finite-sum/constant lintegral identities, the genuine-integrability bridge and ENNReal power identities. SPS19 adds lintegral monotonicity. These are appropriate for the **entire** stopped interval, with divergence retained as infinity. The generic path needs explicit measurability, supplied later by H1 continuity for the canonical solution.

Use the set `{t | 0 < t and ENNReal.ofReal t < T_max and t < tau_A}`, or take the minimum with the finite cutoff before converting the lifetime to a real endpoint. Do not define the full budget using a totalized real integral, or take `toReal` of an unproved finite budget. The zero window has zero budget. None of these measure-theory tools proves universal budget finiteness or constructs an NSE trajectory.

## Gap ranking within this subcollection

| Plan scope | Strongest retained sources | Remaining construction | Assessment |
|---|---|---|---|
| P01 | SP01–SP03; SPS15–SPS16; external SPS29–SPS33 | Actual H1 graph norm/topology/completeness, native gradient uniqueness, Schwartz admission and equivalent solenoidal tests | Substantial representation work; generic separation and completeness primitives already exist |
| P02 | SP04–SP06, SP17–SP18, SP21; SPS15, SPS18, SPS32 | Native compact-test H1 iff first-derivative Fourier multiplier, with no H2 premise | Largest semantic bridge in P01–P08; external spectral-membership directions significantly narrow it |
| P03 | SPS23 and registered sector specification | Fixed six-sector Borel/tie/partition/symmetry proofs | Finite combinatorics and measurability; no new PDE estimate |
| P04 | SP06–SP09, SP19–SP20 | Exact vector projectors; public L2 real-range bridge; orthogonality and reconstruction | Substantial operator/representation assembly, with close source models |
| P05 | SP05, SP17–SP18, SP21 | Physical H1 commutation and solenoidal preservation for the same discontinuous masks | Depends on P02 and the actual P04 operators; not supplied by a smooth-symbol theorem |
| P06 | SP06, SP10, SP18; SPS16 | All-component enstrophy additivity and exact physical/Fourier normalization | Integration of existing norm identities with the new operators |
| P07 | SP11 | Fin 6 specialization and physical substitution | Small algebraic endpoint after P06 |
| P08 | SP12–SP16; SPS19 | Generic path measurability, full stopped-domain construction, finiteness/gauge/sublevel assembly | Standard measure-theory assembly with important infinity/endpoint discipline |

This ranking concerns the spectral portion only. The overall plan's actual R3 norm-controlled local existence, maximal continuation, sharp spatial constant, physical balance identities and literal Fefferman-A class bridge remain separate obligations. The present collection does not discharge them.

## Provenance and evidence boundaries

| Source family | Exact source pin | Evidence attached here |
|---|---|---|
| Native Methboke | `ce7f809ad20b3498a63420a22d17b3c801dfd558` | Full copied source bytes also matched against accepted `afd67db40e71bd1412c82247a78598288deb611e`; selected SP01/SP05 names occur in the retained named type/axiom records for run `44788963412` |
| Recovered Methlib | `53b2318c2b586137b6db74c4d3a41bb0b964b2d8` | Original upstream bytes matched the vendor manifest and accepted Methboke Git source; selected SP04/SP10 names retain their exact scoped external evidence |
| Mathlib | `db584cd6d46c92f209a44c0f1c829460d327499d` | Pinned source inspection; not a newly collected per-theorem audit or newly accepted class endpoint |
| uda-lab/leray-hopf | `e704400f2fb2f26b2ee7f4372c3e1ecbbc82f3dc` | Source only; Lean `4.31.0-rc2`, Mathlib `15a89b2468bc01f1a6230d6e49ef5efc5286e502`; no matching Material compilation/type/axiom evidence |

Material remains at Lean `4.33.0` and its existing Mathlib pin. No pin, imported proof module, compiler policy, root statement or accepted receipt was changed. A private-name cutout is a proof template. A statement whose body has been read is not thereby externally verified. Existing accepted helpers retain only their actual hypotheses and conclusions.

## Search coverage and exclusions

Static searches covered native `QuasiFeffermanA` contracts/Fourier sources, recovered complexification/LC004/LC005/LC001 modules, and pinned Mathlib distribution/Sobolev, Lp, Fourier, continuous-linear-map, Borel-order, finite-sum and ENNReal integration/power sources. Searches specifically examined closed equalizers, compact-test separation, first derivatives without Laplacians, measurable masks, conjugation/reflection, and finite-versus-infinite integral conversion.

The additional external inspection covered `LerayHopf/Analysis/{BoundedMultiplier,SpectralWeakGradient,FourierParseval,RealComplexLpBridge}.lean` and `LerayHopf/R3/{Domain,DivergenceFree,Regularity,EnergyClassConvection,WeightedFourierCommute,RellichBall,SobolevEmbedding,FourierL2}.lean`. This is a focused source search, not a claim that no relevant theorem exists anywhere else. The Buckmaster snapshot is being assessed in the separate parent collection; no conclusion about its coverage is made here.

All copies preserve the original headers/imports and all original comments, including historical status prose. Each cutout is an inclusive, contiguous byte slice with a complete selected declaration body. Full modules provide omitted surrounding namespaces, variables, helper definitions and imports. The catalog records 17 additional supporting-anchor groups instead of duplicating every one as a cutout.

Only static source reads, reference-file preparation and byte/hash checks were performed. No local Lean, Lake, kernel audit, project runner, external CI or Git mutation was performed by this collection task. No new theorem was derived or promoted to A-tier.
