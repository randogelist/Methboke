# MLB17 — `MethbokeAddon.WeakFouriermanB.initial_physicalDissipation_continuousOn_Icc`

Continuity of physical enstrophy on closed subintervals of a smooth initial front; compactness supplies boundedness of the true solution.

**Evidence:** `NAMED_EXTERNAL_TYPE_AXIOM_AUDIT_ACCEPTED` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import MethbokeAddon.WeakFouriermanB.PhysicalEnstrophyEvolution
```

[Raw cutout](../identities/MLB17.lean.txt) · [Full source context](../sources/S26_PhysicalEnstrophyEvolution.lean.txt) · [Pinned source, lines 91–101](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/PhysicalEnstrophyEvolution.lean#L91-L101)

```lean
theorem initial_physicalDissipation_continuousOn_Icc
    (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T))
    (τ : ℝ) (hτT : τ < T) :
    ContinuousOn (fun t => physicalDissipation (u t)) (Icc (0 : ℝ) τ) := by
  apply initial_real_cube_integral_continuousOn_Icc T
    (fun t x => gradientSquareDensity (u t) x) _ τ hτT
  simp_rw [gradientSquareDensity_eq_sum_norm_sq]
  apply continuousOn_finset_sum
  intro j _
  exact (initial_coordinateDerivative_contDiffOn u T hu j).continuousOn.norm.pow 2
```

## Context and reuse boundary

Uniform boundedness of the exact Galerkin family still needs the new stability proof.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal Topology RealInnerProductSpace
namespace MethbokeAddon.WeakFouriermanB
noncomputable section
```

Not uniform H3 or projected C1 by itself. Those compact-trace estimates remain new adapters. Preserve strict τ<T.

Earlier helpers noted by source review (not an exhaustive dependency list): `initial_real_cube_integral_continuousOn_Icc`, `initial_coordinateDerivative_contDiffOn`, `gradientSquareDensity_eq_sum_norm_sq`.

Source blob: `2335a18ccbb0ee6dda235abf5bc1b6bab4df2024`. Cutout SHA-256: `f57d35eb8c46d532149c102a53c5f70458218335821c2583866c76e75f30daf9`.
