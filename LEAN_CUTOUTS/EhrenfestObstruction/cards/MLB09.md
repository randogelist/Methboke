# MLB09 — `SingularClosure.coefficientEnstrophyNonlinearPower_eq_physical`

Physical identification of nonlinear Fourier enstrophy power with minus integral convection dot Laplacian.

**Evidence:** `ACCEPTED_MODULE_SOURCE_REVIEWED_NO_NAMED_DECLARATION_AUDIT` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import SingularClosure.PhysicalBilinear
```

[Raw cutout](../identities/MLB09.lean.txt) · [Full source context](../sources/S35_PhysicalBilinear.lean.txt) · [Pinned source, lines 256–286](https://github.com/randogelist/Methlib/blob/96033dd69c994bec337a87369a6c27256e724980/regularity-B-assembly/Singular-Axiomatic-closure/SingularClosure/PhysicalBilinear.lean#L256-L286)

```lean
theorem coefficientEnstrophyNonlinearPower_eq_physical
    (N : ℕ) (c : FourierCoeff)
    (hsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hreal : SpectralReality c) (hsol : SpectralSolenoidal c) :
    coefficientEnstrophyNonlinearPower N c =
      -(∫ x in unitCube, inner ℝ (convection (finiteSynthesis N c) x)
        (laplacian (finiteSynthesis N c) x)) := by
  rw [finiteSynthesis_laplacian]
  have hswap :
      (∫ x in unitCube, inner ℝ (convection (finiteSynthesis N c) x)
        (finiteSynthesis N (laplacianCoefficient c) x)) =
      ∫ x in unitCube, inner ℝ (finiteSynthesis N (laplacianCoefficient c) x)
        (convection (finiteSynthesis N c) x) := by
    apply integral_congr_ae
    filter_upwards with x
    exact real_inner_comm _ _
  rw [hswap]
  rw [integral_finiteSynthesis_pairing N (laplacianCoefficient c) _
    (convection_continuous (finiteSynthesis_contDiff N c)),
    datumFourierCoeff_convection_finiteSynthesis N c hsupp hreal,
    coefficientEnstrophyNonlinearPower_eq_transport N c hsol]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro k _
  rw [physical_complex_re_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hscalar (r : ℝ) (z w : ℂ) :
      r * (star z * w).re = -(star (-(r : ℂ) * z) * w).re := by
    simp [Complex.star_def, Complex.mul_re, Complex.mul_im] <;> ring
  exact hscalar (laplacianFrequency k) (c k i) (coefficientTransport N c k i)
```

## Context and reuse boundary

Since A=-Δ, P=<B,Au> and W=-P=integral convection dot Δu. Vortex stretching representation requires its own vector-calculus adapter if used.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
set_option Elab.async true
open Set MeasureTheory
open scoped BigOperators ContDiff
namespace SingularClosure
noncomputable section
```

Requires support, spectral reality and solenoidality. Equality has a MINUS sign. No estimate or general time evolution is supplied.

Earlier helpers noted by source review (not an exhaustive dependency list): `integral_finiteSynthesis_pairing`, `datumFourierCoeff_convection_finiteSynthesis`, `convection_continuous`, `coefficientEnstrophyNonlinearPower_eq_transport`.

Source blob: `97b76bf8e8964a03b3ea13f2099900dd75865cd6`. Cutout SHA-256: `6b1ebf8ff572606ee30de3d11e2011c5d2b5b450ecdae5d6f3d09c073c046584`.
