import MethbokeAddon.FDSNR3.Contracts
import MethbokeAddon.FDSN.Phase
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Actual whole-space Fourier bridge

All transforms below are the actual Lebesgue Fourier transform in Mathlib's
2π convention. The slice hypotheses are concrete Schwartz maps, not an
analytic certificate assuming any family conclusion.

Prepared by static inspection only; external compilation and named axiom
audits determine acceptance.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate
open LineDeriv

namespace MethbokeAddon.FDSNR3

noncomputable section

/-- The real-linear complexification of the native Euclidean vector. -/
def complexifyCLM : Vec →L[ℝ] CVec :=
  ({ toFun := complexify
     map_add' := by
       intro v w
       ext i
       simp [complexify]
     map_smul' := by
       intro c v
       ext i
       simp [complexify] } : Vec →ₗ[ℝ] CVec).toContinuousLinearMap

@[simp] theorem complexifyCLM_apply (v : Vec) : complexifyCLM v = complexify v := rfl

@[simp] theorem norm_complexify (v : Vec) : ‖complexify v‖ = ‖v‖ := by
  simp [EuclideanSpace.norm_eq, complexify]

/-- Complexification preserves the actual Schwartz function. -/
def complexifySchwartz (f : 𝓢(Vec, Vec)) : 𝓢(Vec, CVec) :=
  SchwartzMap.postcompCLM complexifyCLM f

@[simp] theorem complexifySchwartz_apply (f : 𝓢(Vec, Vec)) (x : Vec) :
    complexifySchwartz f x = complexify (f x) := rfl

theorem fourierVelocity_eq_schwartz (f : 𝓢(Vec, Vec)) :
    fourierVelocity f =
      ((𝓕 (complexifySchwartz f) : 𝓢(Vec, CVec)) : Vec → CVec) := rfl

theorem schwartz_fourierInv_fourier (f : 𝓢(Vec, CVec)) :
    𝓕⁻ (𝓕 f) = f :=
  FourierTransform.fourierInv_fourier_eq f

theorem schwartz_fourier_fourierInv (f : 𝓢(Vec, CVec)) :
    𝓕 (𝓕⁻ f) = f :=
  FourierTransform.fourier_fourierInv_eq f

/-- Fourier inversion expressed at an actual physical point. -/
theorem physical_fourier_inversion (f : 𝓢(Vec, Vec)) (x : Vec) :
    realify (𝓕⁻ (fourierVelocity f) x) = f x := by
  rw [fourierVelocity_eq_schwartz]
  have h : 𝓕⁻ (fun ξ : Vec => 𝓕 (complexifySchwartz f) ξ) x =
      complexifySchwartz f x := by
    simpa only [SchwartzMap.fourierInv_coe] using
      congrArg (fun g : 𝓢(Vec, CVec) => g x)
        (schwartz_fourierInv_fourier (complexifySchwartz f))
  rw [h, complexifySchwartz_apply, realify_complexify]

theorem schwartz_fourier_injective :
    Function.Injective (𝓕 : 𝓢(Vec, CVec) → 𝓢(Vec, CVec)) := by
  intro f g h
  have hh := congrArg (𝓕⁻ : 𝓢(Vec, CVec) → 𝓢(Vec, CVec)) h
  simpa only [FourierTransform.fourierInv_fourier_eq] using hh

theorem fourierVelocity_injective_on_schwartz {f g : 𝓢(Vec, Vec)}
    (h : fourierVelocity f = fourierVelocity g) : f = g := by
  apply SchwartzMap.ext
  intro x
  rw [← physical_fourier_inversion f x, ← physical_fourier_inversion g x, h]

/-- The scalar Fourier phase convention, with no integrability suppressed. -/
theorem fourier_eq_phase (f : Vec → CVec) (ξ : Vec) :
    𝓕 f ξ = ∫ x : Vec,
      MethbokeAddon.FDSN.phase (-2 * Real.pi * inner ℝ x ξ) • f x := by
  rw [Real.fourier_eq']
  rfl

theorem scalar_fourier_eq_phase (f : Vec → ℂ) (ξ : Vec) :
    𝓕 f ξ = ∫ x : Vec,
      MethbokeAddon.FDSN.phase (-2 * Real.pi * inner ℝ x ξ) * f x := by
  rw [Real.fourier_eq']
  rfl

/-- A continuous complex-linear observation commutes with the actual
Fourier integral of an integrable vector field. -/
theorem fourier_observation (L : CVec →L[ℂ] ℂ)
    {f : Vec → CVec} (hf : Integrable f) (ξ : Vec) :
    𝓕 (fun x => L (f x)) ξ = L (𝓕 f ξ) := by
  rw [Real.fourier_eq, Real.fourier_eq]
  have hi := (Real.fourierIntegral_convergent_iff ξ).mpr hf
  simpa only [Circle.smul_def, map_smul] using L.integral_comp_comm hi

theorem fourier_coordinate {f : Vec → CVec} (hf : Integrable f)
    (ξ : Vec) (i : Fin 3) :
    (𝓕 f ξ) i = 𝓕 (fun x => f x i) ξ :=
  (fourier_observation (EuclideanSpace.proj i : CVec →L[ℂ] ℂ) hf ξ).symm

theorem schwartz_fourier_observation (L : CVec →L[ℂ] ℂ)
    (f : 𝓢(Vec, CVec)) :
    𝓕 (SchwartzMap.postcompCLM L f) =
      SchwartzMap.postcompCLM L (𝓕 f) := by
  apply SchwartzMap.ext
  intro ξ
  exact fourier_observation L f.integrable ξ

/-- Real scalar data have Hermitian Fourier symmetry. -/
theorem scalar_fourier_real_conjugacy (f : Vec → ℝ) (ξ : Vec) :
    𝓕 (fun x : Vec => (f x : ℂ)) (-ξ) =
      conj (𝓕 (fun x : Vec => (f x : ℂ)) ξ) := by
  rw [scalar_fourier_eq_phase, scalar_fourier_eq_phase, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [map_mul, Complex.conj_ofReal, MethbokeAddon.FDSN.conj_phase]
  congr 2
  simp only [inner_neg_right]
  ring

/-- The literal whole-space transform of a real Schwartz velocity has
the conjugacy required by a real inverse reconstruction. -/
theorem fourierVelocity_conjugacy (f : 𝓢(Vec, Vec)) (ξ : Vec) (i : Fin 3) :
    fourierVelocity f (-ξ) i = conj (fourierVelocity f ξ i) := by
  change (𝓕 (complexifySchwartz f : Vec → CVec) (-ξ)) i =
    conj ((𝓕 (complexifySchwartz f : Vec → CVec) ξ) i)
  rw [fourier_coordinate (complexifySchwartz f).integrable,
    fourier_coordinate (complexifySchwartz f).integrable]
  exact scalar_fourier_real_conjugacy (fun x => f x i) ξ

/-- Conjugation and frequency reversal commute with the actual scalar
Fourier integral, including its totalized nonintegrable case. -/
theorem scalar_fourier_conjugate_neg (f : Vec → ℂ) (ξ : Vec) :
    𝓕 (fun x : Vec => conj (f x)) (-ξ) = conj (𝓕 f ξ) := by
  rw [scalar_fourier_eq_phase, scalar_fourier_eq_phase, ← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [map_mul, MethbokeAddon.FDSN.conj_phase]
  congr 2
  simp only [inner_neg_right]
  ring

theorem fourierInv_coordinate {f : Vec → CVec} (hf : Integrable f)
    (x : Vec) (i : Fin 3) :
    (𝓕⁻ f x) i = 𝓕⁻ (fun ξ => f ξ i) x := by
  rw [Real.fourierInv_eq_fourier_neg, fourier_coordinate hf,
    Real.fourierInv_eq_fourier_neg]

/-- A Hermitian scalar spectrum has a real inverse transform. -/
theorem scalar_fourierInv_fixedByConj (f : Vec → ℂ)
    (hf : ∀ ξ : Vec, f (-ξ) = conj (f ξ)) (x : Vec) :
    𝓕⁻ f x = conj (𝓕⁻ f x) := by
  have heq : (fun ξ : Vec => conj (f ξ)) =
      f ∘ (LinearIsometryEquiv.neg ℝ (E := Vec)) :=
    funext (fun ξ => (hf ξ).symm)
  have h := scalar_fourier_conjugate_neg f (-x)
  rw [heq, Real.fourier_comp_linearIsometry] at h
  change 𝓕 f (-(-(-x))) = conj (𝓕 f (-x)) at h
  simpa only [neg_neg, Real.fourierInv_eq_fourier_neg] using h

/-- The inverse transform of an actual Hermitian Schwartz vector spectrum
is exactly the complexification of its real physical representative. -/
theorem inverse_fourier_real_of_hermitian (f : 𝓢(Vec, CVec))
    (hf : ∀ ξ : Vec, ∀ i : Fin 3, f (-ξ) i = conj (f ξ i)) (x : Vec) :
    complexify (realify (𝓕⁻ f x)) = 𝓕⁻ f x := by
  ext1 i
  have hc : (𝓕⁻ f x) i = conj ((𝓕⁻ f x) i) := by
    simpa only [SchwartzMap.fourierInv_coe, fourierInv_coordinate f.integrable] using
      scalar_fourierInv_fixedByConj (fun ξ : Vec => f ξ i) (fun ξ => hf ξ i) x
  have him : ((𝓕⁻ f x) i).im = 0 := by
    have hi := congrArg Complex.im hc
    simp only [Complex.conj_im] at hi
    linarith
  apply Complex.ext
  · rfl
  · change (0 : ℝ) = ((𝓕⁻ f x) i).im
    exact him.symm

/-- Translation is multiplication by the genuine continuous-frequency
character. No periodicity or Fourier-series representation is used. -/
theorem fourier_translation (f : Vec → CVec) (y ξ : Vec) :
    𝓕 (fun x : Vec => f (x + y)) ξ =
      MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y ξ) • 𝓕 f ξ := by
  change VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Vec)
      (f ∘ fun x : Vec => x + y) ξ =
    MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y ξ) •
      VectorFourier.fourierIntegral Real.fourierChar volume (innerₗ Vec) f ξ
  rw [VectorFourier.fourierIntegral_comp_add_right]
  simp [Circle.smul_def, Real.fourierChar_apply, MethbokeAddon.FDSN.phase]

theorem fourierVelocity_translation (v : Field) (y ξ : Vec) :
    fourierVelocity (fun x => v (x + y)) ξ =
      MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y ξ) • fourierVelocity v ξ := by
  exact fourier_translation (fun x => complexify (v x)) y ξ

/-- Fourier symbol of every physical directional derivative of a Schwartz
field. This is the actual Fréchet derivative under the coercion. -/
theorem fourier_directionalDerivative (f : 𝓢(Vec, CVec)) (m ξ : Vec) :
    𝓕 (fun x : Vec => fderiv ℝ (f : Vec → CVec) x m) ξ =
      (2 * (Real.pi : ℂ) * Complex.I) •
        ((inner ℝ ξ m) • 𝓕 f ξ) := by
  have hg : (inner ℝ · m).HasTemperateGrowth :=
    ((innerSL ℝ).flip m).hasTemperateGrowth
  have hderiv : ((∂_{m} f : 𝓢(Vec, CVec)) : Vec → CVec) =
      (fun x : Vec => fderiv ℝ (f : Vec → CVec) x m) := by
    funext x
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv m f x
  have h := congrArg (fun g : 𝓢(Vec, CVec) => g ξ)
    (SchwartzMap.fourier_lineDerivOp_eq f m)
  simpa only [SchwartzMap.fourier_coe, hderiv,
    SchwartzMap.smulLeftCLM_apply_apply hg, smul_apply] using h

/-- Actual trace of the spatial derivative, as a Schwartz scalar field. -/
def schwartzDivergence (f : 𝓢(Vec, CVec)) : 𝓢(Vec, ℂ) :=
  ∑ i : Fin 3, SchwartzMap.postcompCLM
    (EuclideanSpace.proj i : CVec →L[ℂ] ℂ) (∂_{unitVector i} f)

@[simp] theorem schwartzDivergence_apply (f : 𝓢(Vec, CVec)) (x : Vec) :
    schwartzDivergence f x =
      ∑ i : Fin 3, (fderiv ℝ (f : Vec → CVec) x (unitVector i)) i := by
  simp [schwartzDivergence, SchwartzMap.lineDerivOp_apply_eq_fderiv]

theorem fourier_schwartzDivergence (f : 𝓢(Vec, CVec)) (ξ : Vec) :
    𝓕 (schwartzDivergence f) ξ =
      (2 * (Real.pi : ℂ) * Complex.I) *
        ∑ i : Fin 3, (ξ i : ℂ) * (𝓕 f ξ) i := by
  simp only [schwartzDivergence, FourierTransform.fourier_sum, sum_apply,
    schwartz_fourier_observation, SchwartzMap.postcompCLM_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hderiv : ((∂_{unitVector i} f : 𝓢(Vec, CVec)) : Vec → CVec) =
      (fun x : Vec => fderiv ℝ (f : Vec → CVec) x (unitVector i)) := by
    funext x
    exact SchwartzMap.lineDerivOp_apply_eq_fderiv (unitVector i) f x
  have hd := fourier_directionalDerivative f (unitVector i) ξ
  have hdi := congrArg (fun z : CVec => z i) hd
  simpa [SchwartzMap.fourier_coe, hderiv,
    unitVector, EuclideanSpace.inner_single_right, smul_smul, mul_assoc] using hdi

theorem fderiv_complexify {v : Field} {x : Vec} (hv : DifferentiableAt ℝ v x) :
    fderiv ℝ (fun y => complexify (v y)) x =
      complexifyCLM.comp (fderiv ℝ v x) := by
  exact (complexifyCLM.hasFDerivAt.comp x hv.hasFDerivAt).fderiv

theorem schwartzDivergence_complexify (f : 𝓢(Vec, Vec)) (x : Vec) :
    schwartzDivergence (complexifySchwartz f) x =
      (divergence (f : Field) x : ℂ) := by
  rw [schwartzDivergence_apply]
  change (∑ i : Fin 3,
    (fderiv ℝ (fun y => complexify (f y)) x (unitVector i)) i) = _
  rw [fderiv_complexify f.differentiableAt]
  simp [divergence, coordinateDerivative, complexify]

/-- Solenoidality is transported to the literal transverse Fourier
constraint, for the genuine complexification of a real Schwartz field. -/
theorem fourierVelocity_divergence_free (f : 𝓢(Vec, Vec))
    (hf : ∀ x : Vec, divergence (f : Field) x = 0) (ξ : Vec) :
    ∑ i : Fin 3, (ξ i : ℂ) * fourierVelocity f ξ i = 0 := by
  have hz : schwartzDivergence (complexifySchwartz f) = 0 := by
    apply SchwartzMap.ext
    intro x
    change schwartzDivergence (complexifySchwartz f) x = 0
    rw [schwartzDivergence_complexify, hf x, Complex.ofReal_zero]
  have h := fourier_schwartzDivergence (complexifySchwartz f) ξ
  rw [hz, FourierTransform.fourier_zero] at h
  have hc : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num)
      (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hp : (2 * (Real.pi : ℂ) * Complex.I) *
      (∑ i : Fin 3, (ξ i : ℂ) * (𝓕 (complexifySchwartz f) ξ) i) = 0 := h.symm
  exact (mul_eq_zero.mp hp).resolve_left hc

theorem schwartz_plancherel (f : 𝓢(Vec, CVec)) :
    (∫ ξ : Vec, ‖𝓕 f ξ‖ ^ 2) = ∫ x : Vec, ‖f x‖ ^ 2 :=
  SchwartzMap.integral_norm_sq_fourier f

theorem physical_plancherel (f : 𝓢(Vec, Vec)) :
    (∫ ξ : Vec, ‖fourierVelocity f ξ‖ ^ 2) = ∫ x : Vec, ‖f x‖ ^ 2 := by
  simpa only [fourierVelocity_eq_schwartz, complexifySchwartz_apply, norm_complexify] using
    schwartz_plancherel (complexifySchwartz f)

end

end MethbokeAddon.FDSNR3

