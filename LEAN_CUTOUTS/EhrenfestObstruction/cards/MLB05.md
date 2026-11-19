# MLB05 — `SingularClosure.finiteGalerkinRhs_unique_on_Icc`

Uniqueness for the explicit finite coefficient ODE on each forward compact interval.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.GalerkinExistence
```

[Raw cutout](../identities/MLB05.lean.txt) · [Full source context](../sources/S32_GalerkinExistence.lean.txt) · [Pinned source, lines 109–145](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/GalerkinExistence.lean#L109-L145)

```lean
theorem finiteGalerkinRhs_unique_on_Icc (ν : ℝ) (N : ℕ)
    (f g : ℝ → FiniteGalerkinState N) (T : ℝ)
    (hf : ContinuousOn f (Ici 0)) (hg : ContinuousOn g (Ici 0))
    (hf' : ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt f (finiteGalerkinRhs ν N (f t)) (Ici 0) t)
    (hg' : ∀ t : ℝ, 0 ≤ t →
      HasDerivWithinAt g (finiteGalerkinRhs ν N (g t)) (Ici 0) t)
    (h0 : f 0 = g 0) : EqOn f g (Icc 0 T) := by
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
  have hfc : ContinuousOn f (Icc 0 T) := hf.mono hsub
  have hgc : ContinuousOn g (Icc 0 T) := hg.mono hsub
  obtain ⟨Mf, hMf⟩ := isCompact_Icc.exists_bound_of_continuousOn hfc
  obtain ⟨Mg, hMg⟩ := isCompact_Icc.exists_bound_of_continuousOn hgc
  let M : ℝ := max Mf Mg
  have hfM : ∀ t ∈ Icc (0 : ℝ) T,
      f t ∈ closedBall (0 : FiniteGalerkinState N) M := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    exact (hMf t ht).trans (le_max_left Mf Mg)
  have hgM : ∀ t ∈ Icc (0 : ℝ) T,
      g t ∈ closedBall (0 : FiniteGalerkinState N) M := by
    intro t ht
    rw [mem_closedBall, dist_zero_right]
    exact (hMg t ht).trans (le_max_right Mf Mg)
  have hC1 : ContDiff ℝ 1 (finiteGalerkinRhs ν N) :=
    (contDiff_finiteGalerkinRhs ν N).of_le (by norm_num)
  obtain ⟨K, hK⟩ :=
    (hC1.contDiffOn (s := closedBall (0 : FiniteGalerkinState N) M)).exists_lipschitzOnWith
      one_ne_zero (convex_closedBall _ _) (isCompact_closedBall _ _)
  apply ODE_solution_unique_of_mem_Icc_right
    (v := fun _ => finiteGalerkinRhs ν N)
    (s := fun _ => closedBall (0 : FiniteGalerkinState N) M) (K := K)
    (fun _ _ => hK) hfc
    (fun t ht => (hf' t ht.1).mono (fun _ hs => ht.1.trans hs))
    (fun t ht => hfM t ⟨ht.1, ht.2.le⟩) hgc
    (fun t ht => (hg' t ht.1).mono (fun _ hs => ht.1.trans hs))
    (fun t ht => hgM t ⟨ht.1, ht.2.le⟩) h0
```

## Context and reuse boundary

Forward interval formulation; transporting to two-sided flow remains an adapter.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
open Set Metric
open scoped ContDiff BigOperators
namespace SingularClosure
noncomputable section
```

Compares finite state curves only on nonnegative-time interval; not PDE uniqueness or spectral stability. Not needed if canonicalFamily is used directly.

Earlier helpers noted by source review (not an exhaustive dependency list): `contDiff_finiteGalerkinRhs`, `ODE_solution_unique_of_mem_Icc_right`.

Source blob: `99a1d77891985e082e015e055cef7c3980c2e5fc`. Cutout SHA-256: `c69db1fa5c6dee6b2b705724fb00d4739564688ac1224ca8ea4230671ad34c36`.
