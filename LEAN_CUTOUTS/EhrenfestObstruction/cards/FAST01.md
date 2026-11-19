# FAST01 — `MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION`

Absorb self-error nonlinear enstrophy term using reduced positive viscosity allocation.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import MethbokeAddon.WeakFouriermanB.PhysicalNonlinear
```

[Raw cutout](../identities/FAST01.lean.txt) · [Full source context](../sources/S19_PhysicalNonlinear.lean.txt) · [Pinned source, lines 262–286](https://github.com/randogelist/Methboke/blob/9ae4429b9c218c109bddaac2f993f1cc5bd66aa8/Material/MethbokeAddon/WeakFouriermanB/PhysicalNonlinear.lean#L262-L286)

```lean
theorem PHYSICAL_NONLINEAR_ABSORPTION :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ v : Field,
      ContDiff ℝ ∞ v → SpatialPeriodic v → MeanZero v →
      2 * (∫ x in unitCube, inner ℝ (convection v x) (laplacian v x)) ≤
        ν * physicalLaplacianSquare v + C / ν ^ 3 * physicalDissipation v ^ 3 := by
  obtain ⟨K, hK, hb⟩ := PHYSICAL_NONLINEAR_REAL_BOUND
  refine ⟨(2 * K) ^ 4 + 1, by positivity, ?_⟩
  intro ν hν v hv hp hz
  have hD := physical_dissipation_nonneg v
  have hZ := physicalLaplacianSquare_nonneg v
  calc
    _ ≤ 2 * abs (∫ x in unitCube, inner ℝ (convection v x) (laplacian v x)) :=
      mul_le_mul_of_nonneg_left (le_abs_self _) (by norm_num)
    _ ≤ 2 * (K * physicalDissipation v ^ (3 / 4 : ℝ) *
        physicalLaplacianSquare v ^ (3 / 4 : ℝ)) :=
      mul_le_mul_of_nonneg_left (hb v hv hp hz) (by norm_num)
    _ = 2 * K * physicalDissipation v ^ (3 / 4 : ℝ) *
        physicalLaplacianSquare v ^ (3 / 4 : ℝ) := by ring
    _ ≤ ν * physicalLaplacianSquare v +
        (2 * K) ^ 4 / ν ^ 3 * physicalDissipation v ^ 3 :=
      nonlinear_three_quarter_absorption hK hD hZ hν
    _ ≤ _ := by
      apply add_le_add le_rfl
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hD _)
      exact div_le_div_of_nonneg_right (by linarith) (pow_nonneg hν.le _)
```

## Context and reuse boundary

One-sided sign is appropriate for convection paired with laplacian in error energy identity. Must build forced-error derivative identity; solution-only derivative theorem does not apply to w_N.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal NNReal RealInnerProductSpace
namespace MethbokeAddon.WeakFouriermanB
noncomputable section
```

One-sided signed bound, not an absolute-value estimate. Apply with a positive viscosity fraction. Forced quadratic derivative remains new; no GalerkinSolution premise is needed here.

Earlier helpers noted by source review (not an exhaustive dependency list): `physicalLaplacianSquare`, `PHYSICAL_NONLINEAR_REAL_BOUND`, `physical_dissipation_nonneg`, `physicalLaplacianSquare_nonneg`, `nonlinear_three_quarter_absorption`.

Source blob: `1b3ecaf2897c9a22610d4d328e08337e5402528a`. Cutout SHA-256: `d1d6377e6f6db74ffdcc488892c498c85695f8b14238f1223a156f0f3e764b90`.
