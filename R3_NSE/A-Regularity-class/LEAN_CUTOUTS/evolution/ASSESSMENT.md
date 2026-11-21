# Evolution references for P10, P11 and P19

## Finding and collection scope

**The largest evolution gap is the actual whole-space H1 initial-value constructor with a lifespan uniform on H1 balls.** The accepted native periodic theory supplies a genuine construction and a useful maximal-continuation architecture, but no attained accepted theorem instantiates that theory on arbitrary physical H1 data on R3. The second major gap is the literal Fefferman-A competitor bridge, including the uniform finite-endpoint control needed for continuation.

This collection contains **14 complete declaration cutouts and 12 byte-preserved full source modules**. The [catalog](catalog.json) records the exact source commits, imports, namespaces, line intervals, SHA256 values, retained premises and evidence references. Eight cutouts have matching named external type-and-axiom reports; two have matching compiled-module evidence only; four are upstream source-only references. Five additional source leads are recorded without redistribution.

The collection basis is `randogelist/Methboke`, branch `AC-Integration`, commit `ce7f809ad20b3498a63420a22d17b3c801dfd558`. All files here are reference `.lean.txt` files, outside `Material`. They are not standalone modules or new proof endpoints. No Lean, Lake, kernel, project runner or archived script was executed; no compiler or axiom audit was initiated. The Fefferman-D project goal and all existing accepted scopes remain unchanged.

## Ranked gaps

| Priority | Plan edge | What is available | What must actually be proved |
|---|---|---|---|
| 1 | **P10: physical R3 H1 local theory** | EV02–EV04 construct periodic smooth solutions from finite Galerkin bounds and recover the physical PDE. EVL01 is a newly inspected whole-space H^m fixed-point constructor for m >= 3. | For every actual solenoidal H1 datum, construct a solution in C_t H1 with L2_t H2 regularity and the actual PDE/initial trace, uniqueness, and a positive lifespan controlled only by viscosity and an H1 bound. Include zero data. No supplied-solution record, H3-only admission or compact-support premise may replace this. |
| 2 | **P19: literal competitor admission and A4 endpoint control** | EV11 and EV13 derive pressure control/comparison for supplied H3 solutions. EVL04 compares actual smooth finite-energy whole-space solutions using a bounded reference velocity and gradient. | Identify a literal smooth finite-energy competitor with the canonical solution on closed slabs and obtain the uniform H1/enstrophy control required to cross a hypothetical finite canonical endpoint. Equality on every R < Tmax alone does not provide a bound uniform as R tends to Tmax. |
| 3 | **P19: pressure recovery and smoothness through time zero** | EV04 gives full periodic recovery. EVL03 recovers smooth whole-space velocity and pressure from an all-order Fourier Sobolev trajectory and its Duhamel equation. EVL05 smooths an already given mild trajectory away from the initial boundary. | Construct and identify pressure, prove all spatial/time regularity on [0,R] for Schwartz data with R < Tmax, handle the initial boundary, and derive the global energy requirement when Tmax is infinite. Prove equality of pressure gradients before choosing the smooth time gauge. |
| 4 | **P11: canonical maximality, strong restart and continuation** | EV05–EV08 provide a complete periodic pattern: compatible fronts, a supremum lifetime, uniqueness, actual restart gluing and continuation from a uniform H1 bound. | Supply the R3 local existence and uniqueness instances, then prove maximality and continuation for the same actual trajectory. Restart strictly before the hypothetical finite endpoint; do not assume an endpoint H1 trace. This edge is structurally reusable once P10 is complete. |

These are substantive analytic or physical-instance obligations. The generic scalar budget and good-time arguments elsewhere in the plan do not discharge them. The registered class can use canonical strong restarts; global Leray–Hopf existence, full weak restart membership and the complete weak–strong QFA tail theorem are not prerequisites of this shorter route.

## Exact collected declarations

Short names below are completed by the namespaces and imports in the catalog.

| ID | Declaration | Scope and use |
|---|---|---|
| EV01 | `InitialClassicalFront` | Exact periodic PDE/initial/pressure contract; a definition rather than existence. |
| EV02 | `uniform_H1_local_initial_classical_front_exists` | Actual smooth periodic local construction with a lifespan uniform on H1 balls. The full module includes the underlying Galerkin constructor. |
| EV03 | `local_sobolev_flow_of_uniform_H2` | Constructs the untruncated periodic Sobolev trajectory from uniform finite-Galerkin estimates. Its displayed bound is discharged in the native local theorem. |
| EV04 | `LocalSobolevFlow.initialClassicalFront` | Recovers smooth actual velocity, normalized pressure and the physical PDE, including time zero. |
| EV05 | `maximal_classical_front_exists_of_front` | Builds a maximal trajectory from one actual local front, using proved periodic overlap uniqueness. |
| EV06 | `maximal_classical_front_unique` | Unique extended lifetime and same velocity/pressure strictly before it. |
| EV07 | `initial_front_extend_from_restart` | Splices a longer physical front from an interior restart, preserving the entire old trajectory. |
| EV08 | `maximal_classical_lifetime_eq_top_of_uniform_H1` | Excludes a finite maximal lifetime from a uniform preterminal H1 bound. |
| EV09 | `normalized_pressure_eq_of_gradient_eq` | Equal gradients give a constant difference; cube means remove the constant. The last normalization is domain-specific. |
| EV10 | `StrongSolutionOnIcc` | Actual supplied H3 whole-space solution contract; no local existence conclusion. |
| EV11 | `StrongSolutionOnIcc.pressureGradient_memLp` | Derives L2 pressure-gradient integrability from the supplied H3 PDE and L2 forcing. |
| EV12 | `strongSolution_of_compact_slab` | Admits a supplied smooth solution into H3 when a single compact set contains its velocity support for the entire slab. |
| EV13 | `strong_unique` | Same-data uniqueness of two supplied H3 solutions, with a uniformly bounded derivative representation for the reference. |
| EV14 | `ReferenceConstructionFromAbsorption` | Explicit uninhabited construction interface retained by historical QFA; its definition does not prove reference existence. |

The full source modules preserve their original imports, comments, local declarations and proof bodies. In particular, some native comments predate later acceptance and still say “prepared”; their historical comments have not been rewritten. Evidence is assigned by exact matching source and retained reports, not by those labels. A cutout can depend on preceding private declarations in its full module and is not asserted to elaborate in isolation.

## Newly inspected whole-space source leads

Repository: `tristanbuckmaster/navier-stokes`, exact commit `ad53419de079eb8f95f60313473374624a348546`. Its source environment is **Lean 4.33.1 / Mathlib 0df444a360eaa60ab8c11dca51a86af692955474**, different from the native environment. The acquired README states that the patched package was not rebuilt when assembled. No matching native acceptance is inferred.

No licensing grant was found in the acquired snapshot. These entries therefore retain names, exact URLs, source hashes and scope descriptions in `inspected_source_leads_not_redistributed`; no full module or long cutout from that repository is included here.

- **EVL01 — actual higher-regularity local construction.** `Breakdown.SmoothFlow.exists_local_varConst`, `lean/Breakdown/Uniqueness/RegLocal.lean:12–34`, constructs a Fourier solution from measurable real-symmetric solenoidal data with an H^m bound, **m >= 3**. The proof calls `exists_varConst_fixedPoint`; its body obtains proved contraction estimates, controls the iterates and constructs their limit. This is a genuine constructor, unlike the older supplied-H3 record. Its lifespan depends on the H^m bound, so it does not yet satisfy P10's arbitrary H1 datum and H1 lifespan requirements.
- **EVL02 — continuation from an explicit bound.** `Breakdown.SmoothFlow.exists_symbolFlow_of_homBound`, `RegGlueAux.lean:45–109`, uses the H3 local constructor, a higher-norm a priori estimate and concatenation to reach a fixed horizon. It explicitly assumes one homogeneous-H1 bound for every shorter symbol flow from the datum. Proving that bound is not a conclusion of the theorem.
- **EVL03 — physical smooth velocity and pressure recovery.** `Breakdown.SmoothFlow.isSolutionOn_physField`, `RegPhys.lean:12–27`, derives actual momentum, divergence and joint smoothness on a closed slab from **all-order** `IsHsCurve`, the Duhamel symbol equation and solenoidal/reality conditions. It is useful for P19 after those all-order premises are constructed, including the initial boundary. It does not itself start from arbitrary H1 data.
- **EVL04 — broader finite-energy competitor comparison.** `Breakdown.eq_of_isSolutionOn`, `SmoothUniqueness.lean:114–204`, assumes two actual smooth solutions on a closed slab, a uniform finite slab energy bound for each, the same initial velocity, and a bound on both reference velocity and its spatial derivative. The competitor need not be H3. Its localized difference-energy and pressure argument improves the comparison source material. It still does not derive bounded enstrophy or a uniform H1 bound for an arbitrary literal competitor up to a hypothetical finite Tmax. It therefore does not close A4 by itself.
- **EVL05 — conditional mild smoothing.** `Breakdown.FarField.mildSmoothingOfLocalGain_holds`, `CertTorus/MildSmoothing.lean:111–151`, proves smoothing from `LocalGain`, `MildRestrict` and `DerivSobolev` for a supplied mild trajectory. It yields all-order homogeneous Sobolev regularity after a positive separation from the initial time. The nearby `PicardConverges` statement also assumes that mild trajectory. The directory name does not imply a spatial torus: these statements use a whole-space Fourier carrier.

**Viscosity is normalized in these leads.** Their heat symbol and `IsSolutionOn` encode viscosity one. The present class quantifies over every nu > 0, so a proved scaling/transport adapter and exact native operator identification remain necessary. The same repository's `IsH1Field` interface also includes spatial smoothness; its name alone is not arbitrary weak-H1 admission. None of these leads is imported into the native build by this collection.

## Evidence and environment boundary

| Source group | Exact pin | Evidence carried by this collection |
|---|---|---|
| Native Methboke periodic modules | `afd67db40e71bd1412c82247a78598288deb611e` | All eight copied module byte sequences match this accepted commit and the collection base. Eight selected theorems have named PASS type/axiom reports in run `44788963412`; EV01 has compiled-module evidence only. |
| Recovered Methlib QFA | `53b2318c2b586137b6db74c4d3a41bb0b964b2d8` | EVS12 exactly matches its native vendor copy at accepted `afd67db4`. EV14 is a definition in a compiled PASS module, not a separately named audit root and not an inhabitant of its construction proposition. |
| OpenAI H3 source subset | `f9e8bc5b38b6e212696e8a30e3e91517af887bbd` | Three full modules and four cutouts; hashes match the earlier pinned source report. Source-only here, with Lean 4.34.0-rc2 / Mathlib 85e3a25e006c35636f0e53b0e9296caca2685bc0. |
| Newly inspected Buckmaster leads | `ad53419de079eb8f95f60313473374624a348546` | Source metadata only; a separate toolchain and no matching native compiler/type/axiom evidence. |

The native environment is **Lean 4.33.0 / Mathlib db584cd6d46c92f209a44c0f1c829460d327499d**. The retained evidence archive is `audits/material-afd67db4-qfa-accepted/evidence.zip`; every genuinely matching reference in the catalog names its exact report member, module receipt and, where present, named audit. Each named report uses only `propext`, `Classical.choice` and `Quot.sound`. Module-only evidence is not relabeled as a named theorem audit. New carriers, instances, adapters and endpoints will each require their own matching authorized external verification.

## Search coverage and precise non-findings

The local search covered the native periodic local/Galerkin/maximal/restart/pressure sources, the recovered upstream seven-file H3/comparison subset, both Methlib snapshots (`53b2318c…`, 2,124 Lean files; `96033dd…`, 2,245 Lean files), and targeted evolution/recovery modules in the new Buckmaster source. Whole-snapshot declaration-header searches were followed by direct reads of the relevant constructor and interface bodies. These inventory counts include duplicate and unrelated historical material; they are not proof-completion percentages.

In Methlib, the available finite-Galerkin existence is periodic and the QFA physical reference constructor remains explicit. The older upstream `strongSolution_of_compact_slab` is an admission theorem for a given compactly supported solution, not an initial-value constructor; compact support is not available for general Schwartz evolution or arbitrary H1 restarts. Its H3 uniqueness theorem compares two H3 inputs and cannot silently admit the literal finite-energy category.

The newly acquired UDA Leray–Hopf source is handled by the collection coordinator. This evolution subset does not depend on global weak existence or claim a UDA result. Broad remote source-search coverage and source-license metadata are likewise recorded by the coordinator.

**No ready native R3 H1 constructor or complete literal A4 admission/continuation theorem was attained in this subset.** That statement records the current search result and exact remaining target; it is not a claim that no such result exists anywhere. The new higher-regularity constructor, physical pressure recovery and broader uniqueness leads materially improve the available references without completing those target instances.
