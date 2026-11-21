# Largest Lean gaps for the NSE-A class theorem

**Source acquisition completed; the native theorem remains open.** The ranking below concerns the registered twenty-endpoint target and the inspected source set. It does not assert that a theorem is absent from every Lean project.

The canonical target remains $a\in\mathfrak C_\nu^A\iff J_{6,A}<\infty\iff T_{\max}=\infty$, at the registered cutoff $\tau_A=8\|a\|_2^4/(27\pi^4\nu^5)$. Literal Fefferman-A identification is the additional P19 endpoint.

| Rank | Gap | Endpoints | What the attained material changes |
|---|---|---|---|
| 1 | Actual R3 H1 local/maximal evolution | P10–P11 | Genuine periodic constructors and an external higher-Sobolev constructor provide models; the native H1-controlled R3 constructor is still missing. |
| 2 | Sharp spatial constant | P09 | Nonsharp Sobolev and H1-to-L6 source is available; the registered sharp constant is not formally admitted. |
| 3 | Physical PDE evolution and bootstrap | P12–P17 | Actual R3 convection source and accepted scalar identities help; time regularity and the actual trajectory estimates remain. |
| 4 | Literal solution-category bridge | P19 | Pressure and comparison sources help; all-order propagation and terminal H1 control remain. |
| 5 | Physical H1/Fourier/projector bridge | P01–P06 | Substantial new derivative, multiplier and reality source narrows the required native adapters. This is the first implementation layer. |
| 6 | Full-budget and class assembly | P07–P08, P18 | Most scalar/measure tools are available; instantiation waits for the actual fields and canonical trajectory. |

## G01. Actual whole-space H1 local and maximal evolution

**Required native statement.** For each physical H1_sigma(R3) datum and nu>0, construct an actual unique local NSE solution with C_t H1 / L2_t H2 regularity and lifespan controlled by its H1 norm; construct its maximal continuation and prove the bounded-H1 continuation criterion.

**Attained.** Native periodic Galerkin local existence, norm-controlled lifespan, maximal development, overlap uniqueness and restart proofs are collected. A new external source lead has a genuine Fourier H^m fixed-point constructor for m>=3, rather than only a supplied-solution record.

**Still missing.** The periodic theorem has smooth periodic mean-zero data. The higher-Sobolev external constructor uses viscosity one and a stronger norm. Neither supplies the required native arbitrary-H1 R3 constructor. Heat/Leray estimates, fixed point, initial trace, uniqueness, H1-controlled lifetime and all physical adapters remain.

**Proof boundary.** A StrongSolutionOnIcc record or ReferenceConstructionFromAbsorption proposition is an interface, not an inhabitant proving existence.

**Exact cutouts:** [EV01](cards/EV01.md), [EV02](cards/EV02.md), [EV03](cards/EV03.md), [EV04](cards/EV04.md), [EV05](cards/EV05.md), [EV06](cards/EV06.md), [EV07](cards/EV07.md), [EV08](cards/EV08.md), [EV10](cards/EV10.md), [EV12](cards/EV12.md), [EV14](cards/EV14.md).

**Additional inspected leads:** EVL01, EVL02 in [SOURCE_LEADS.json](SOURCE_LEADS.json); these are source metadata only.

## G02. Sharp spatial admission for the registered numerical cutoff

**Required native statement.** On the same physical R3 H1 space prove ||v||_6 <= S6 ||grad v||_2 with S6^6=16/(27*pi^4), plus vector/tensor extensions and the H2 Hessian-Laplacian identities used by enstrophy.

**Attained.** Pinned Mathlib gives a genuine compact-C1 Sobolev estimate with another explicit constant; external gns_L6_of_memH1_R3 gives L6 membership; the accepted cutoff lemma rewrites a supplied sixth-power equality.

**Still missing.** Extend to the native physical H1 carrier and establish admissibility of the registered S6, not only its arithmetic. ES16 is L2 times gradient-L2 times a Schwartz L-infinity test bound, not the required sharp estimate.

**Proof boundary.** A proved arbitrary constant changes the associated cutoff. L6 membership, an extremal calculation or the arithmetic identity alone does not justify the frozen tau_A.

**Exact cutouts:** [ES01](cards/ES01.md), [ES06](cards/ES06.md), [ES13](cards/ES13.md), [ES16](cards/ES16.md).

## G03. Actual physical time evolution, balances and continuation bootstrap

**Required native statement.** For the constructed R3 strong solution, prove E and Y absolutely continuous on every closed [0,R] with 0<=R<Tmax, derive E'= -2*nu*Y and Y'+nu*Z <= pi^(-4)*nu^(-3)*Y^3 almost everywhere, and prove the small-product temporal invariant.

**Attained.** Actual R3 source proofs of H1 convection integrability, weak IBP and antisymmetry; native periodic enstrophy evolution and continuation patterns; finite-interval scalar energy helpers; Mathlib AC FTC; an already named-audited integral Gronwall theorem.

**Still missing.** Derive time regularity and the physical integral inequality from the actual strong trajectory, with all pressure/spatial cancellations and norms matched. Prove the first-exit bootstrap and same-path continuation. Existing scalar lemmas do not construct the PDE inputs.

**Proof boundary.** Do not use the global-LH wrapper while proving globality; do not transfer periodic Poincare to R3; do not substitute the historical ES12 threshold ED<4*pi^2*nu^4 for nu^4/S6^6.

**Exact cutouts:** [ES02](cards/ES02.md), [ES03](cards/ES03.md), [ES04](cards/ES04.md), [ES05](cards/ES05.md), [ES06](cards/ES06.md), [ES07](cards/ES07.md), [ES08](cards/ES08.md), [ES09](cards/ES09.md), [ES10](cards/ES10.md), [ES11](cards/ES11.md), [ES12](cards/ES12.md), [ES14](cards/ES14.md), [ES15](cards/ES15.md).

**Additional inspected leads:** EVL02 in [SOURCE_LEADS.json](SOURCE_LEADS.json); these are source metadata only.

## G04. Literal Fefferman-A category and terminal control

**Required native statement.** Construct velocity/pressure smoothness through t=0 for Schwartz data on all available finite slabs, and identify any literal smooth finite-energy Fefferman competitor with a global canonical H1 development.

**Attained.** Native pressure-normalization proof, supplied-H3 whole-space pressure/comparison sources, and new external leads for actual physical recovery from all Sobolev orders and smooth finite-energy comparison.

**Still missing.** Prove all-order propagation and pressure recovery, arbitrary-nu transport where needed, and the finite-slab H1/enstrophy admission necessary to rule out a finite canonical endpoint. Smoothness is lifetime-qualified until globality is proved.

**Proof boundary.** Agreement on every R<Tmax does not imply a uniform H1 bound as R increases to finite Tmax. Smooth finite L2 energy alone must not be silently strengthened to the strong competitor category.

**Exact cutouts:** [EV04](cards/EV04.md), [EV09](cards/EV09.md), [EV10](cards/EV10.md), [EV11](cards/EV11.md), [EV12](cards/EV12.md), [EV13](cards/EV13.md).

**Additional inspected leads:** EVL03, EVL04, EVL05 in [SOURCE_LEADS.json](SOURCE_LEADS.json); these are source metadata only.

## G05. Native physical H1, Fourier and six-projector identification

**Required native statement.** Identify native real compact-test H1 with the spectral membership construction; prove the first-derivative Fourier identity both ways; construct six actual real-preserving vector projections and derivative/solenoidal commutation.

**Attained.** Complete equalizers and real compact-test separation; actual spectral derivative witnesses; weighted Fourier L2 representatives and reverse membership; bounded measurable scalar L2 multipliers; real L2 Fourier Hermitian symmetry by density.

**Still missing.** Construct the closed physical gradient graph and its norm. Prove the component/vector/compact-test adapters and the full real-range equivalence; specialize to the fixed six sectors, prove disjointness/reconstruction and physical charge additivity. External pins and private proof templates need explicit native handling.

**Proof boundary.** Existing native gradient_fourier_ae has a combined gradient/Laplacian witness interface. Do not add an H2 assumption to the H1 projector endpoint or apply a smooth multiplier API to sharp cones.

**Exact cutouts:** [SP01](cards/SP01.md), [SP02](cards/SP02.md), [SP03](cards/SP03.md), [SP04](cards/SP04.md), [SP05](cards/SP05.md), [SP06](cards/SP06.md), [SP07](cards/SP07.md), [SP08](cards/SP08.md), [SP09](cards/SP09.md), [SP10](cards/SP10.md), [SP17](cards/SP17.md), [SP18](cards/SP18.md), [SP19](cards/SP19.md), [SP20](cards/SP20.md), [SP21](cards/SP21.md).

## G06. Exact stopped-budget and datum-class assembly

**Required native statement.** Assemble the factor-six inequality and full ENNReal terminal budgets for the same canonical trajectory; derive finiteness/gauge/sublevel equivalences and the complete datum-class iff.

**Attained.** Finite Cauchy-Schwarz, squared-norm integrability, monotone nonnegative integration, finite real-integral conversion, ENNReal powers and scalar continuation selectors are available.

**Still missing.** Supply the physical charges and canonical solution from earlier endpoints, exact measurability, full improper endpoint identity and zero-data cases; prove both directions of the class theorem. This is primarily assembly once the larger constructions exist.

**Proof boundary.** Never replace the full endpoint budget by separate compact-interval finiteness, or convert an infinite extended lifetime/budget to a misleading real zero.

**Exact cutouts:** [SP10](cards/SP10.md), [SP11](cards/SP11.md), [SP12](cards/SP12.md), [SP13](cards/SP13.md), [SP14](cards/SP14.md), [SP15](cards/SP15.md), [SP16](cards/SP16.md), [ES03](cards/ES03.md), [ES05](cards/ES05.md), [ES06](cards/ES06.md).

## A concrete improvement to P15

The preferred scalar route is now

$$
\operatorname{AC}(Y)\quad\text{and}\quad Y'\le\kappa Y^3
\;\Longrightarrow\;
Y(t)\le Y(0)+\int_0^t\kappa Y(r)^3\,dr
\;\Longrightarrow\;
Y(t)\le Y(0)\exp\!\left(\kappa\int_0^tY(r)^2\,dr\right),
\qquad \kappa=\pi^{-4}\nu^{-3}.
$$

[ES02](cards/ES02.md) supplies the real AC fundamental theorem of calculus.
[ES03](cards/ES03.md), `QFA.Endpoints.Comparison.CRITICAL_RELATIVE_ENERGY_GRONWALL`, has an exact previously named audit in the retained accepted run. Set its coefficient to `kappa * Y^2`, energy to `Y`, and initial bound to `Y(0)` on each compact strong slab. The actual H1 continuity supplies coefficient continuity; the physical AC estimate supplies the Volterra inequality.

Thus the missing proof is the physical PDE-to-integral-inequality adapter. A new general scalar AC Gronwall theorem is not required by this route. [ES07](cards/ES07.md) remains a valid alternative only after its stronger continuous-derivative/Laplacian premises are established; its selected declarations have compiled-module evidence rather than a directly named audit.

## The first native batch after source acquisition

1. Use SP03 to prove uniqueness of native real compact-test gradients.
2. Use SP02 to construct the complete closed gradient graph, independently of Fourier theory.
3. Adapt SP17/SP18/SP21 to obtain the native two-way H1 Fourier bridge, retaining the actual vector and compact-test meanings.
4. Construct the fixed six projectors using SP19 or the native pinned L2 indicator tools; prove the real-range step explicitly with the SP20 pattern.
5. Assemble SP10–SP16 for the physical charge and full-endpoint budget theorem.

The plan endpoints remain proposed until prepared native sources receive matching authorized external evidence. All copied source is reference text outside the active build. No local Lean, Lake, kernel audit or runner was executed.

## Search and evidence coverage

The collection inspected the current native/vendor sources, the pinned Mathlib tree, the previously recovered Methlib sources, the pinned OpenAI R3 H3 sources, and newly acquired uda-lab and Buckmaster source archives. Public code/repository searches supplied further leads; empty search results are not treated as global absence proofs. Selected declarations and their immediate context were read; full transitive external dependency acceptance has not been performed.

[Source environments](SOURCE_ENVIRONMENTS.json) record the different compiler/Mathlib pins. Existing named native acceptance remains attached to the original scoped declarations. The new external source and the five metadata-only leads are not native accepted endpoints.

The separate universal statement $\mathfrak C_\nu^A=\mathcal S_\sigma(\mathbb R^3)$ remains open. It is not a premise to discharge in order to prove the conditional class equivalence.
