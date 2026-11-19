import SingularClosure.InitialCutoffBounds
import SingularClosure.LerayPressure
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Actual pressure Fourier coefficients are annihilated by Leray projection

The scalar Fourier derivative identity is obtained from the existing
physical periodic integration-by-parts theorem by embedding the scalar in
the first vector component. The zero frequency is handled explicitly.
No Fourier completeness or infinite-series representation is assumed.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff

namespace MethbokeAddon.EhrenfestObstruction

noncomputable section

/-- A scalar field embedded as the first component of a physical vector field. -/
def pressureAsFirstComponent (p : Vec → ℝ) : Field :=
  fun x => p x • unitVector (0 : Fin 3)

/-- The actual scalar pressure Fourier integral. -/
def scalarPressureFourierCoeff (p : Vec → ℝ) (k : Frequency) : ℂ :=
  ∫ x in unitCube, star (fourierCharacter k x) * (p x : ℂ)

@[simp]
theorem pressureAsFirstComponent_apply_zero (p : Vec → ℝ) (x : Vec) :
    pressureAsFirstComponent p x 0 = p x := by
  simp [pressureAsFirstComponent, unitVector]

theorem pressureAsFirstComponent_contDiff
    (p : Vec → ℝ) (hp : ContDiff ℝ ∞ p) :
    ContDiff ℝ ∞ (pressureAsFirstComponent p) := by
  exact hp.smul contDiff_const

theorem pressureAsFirstComponent_periodic
    (p : Vec → ℝ) (hp : SpatialPeriodic p) :
    SpatialPeriodic (pressureAsFirstComponent p) := by
  intro x i
  change p (x + unitVector i) • unitVector (0 : Fin 3) =
    p x • unitVector (0 : Fin 3)
  rw [hp x i]

/-- The scalar pressure coefficient is an integrable physical Fourier integral. -/
theorem scalarPressureFourierIntegrand_integrableOn
    (p : Vec → ℝ) (hp : ContDiff ℝ ∞ p) (k : Frequency) :
    IntegrableOn (fun x : Vec => star (fourierCharacter k x) * (p x : ℂ))
      unitCube volume := by
  have h := datumFourierIntegrand_integrableOn
    (pressureAsFirstComponent_contDiff p hp).continuous k (0 : Fin 3)
  change IntegrableOn (fun x : Vec =>
    star (fourierCharacter k x) * (pressureAsFirstComponent p x 0 : ℂ))
    unitCube volume at h
  simpa only [pressureAsFirstComponent_apply_zero] using h

theorem datumFourierCoeff_pressureAsFirstComponent_zero
    (p : Vec → ℝ) (k : Frequency) :
    datumFourierCoeff (pressureAsFirstComponent p) k 0 =
      scalarPressureFourierCoeff p k := by
  simp only [datumFourierCoeff, datumFourierIntegrand,
    scalarPressureFourierCoeff, pressureAsFirstComponent_apply_zero]

theorem pressureAsFirstComponent_coordinateDerivative_zero
    (p : Vec → ℝ) (hp : ContDiff ℝ ∞ p) (j : Fin 3) (x : Vec) :
    coordinateDerivative (pressureAsFirstComponent p) j x 0 =
      fderiv ℝ p x (unitVector j) := by
  have hd : HasFDerivAt (fun y : Vec => p y • unitVector (0 : Fin 3))
      ((fderiv ℝ p x).smulRight (unitVector (0 : Fin 3))) x :=
    ((hp.differentiable (by simp) x).hasFDerivAt).smul_const (unitVector (0 : Fin 3))
  change (fderiv ℝ (fun y : Vec => p y • unitVector (0 : Fin 3))
    x (unitVector j)) 0 = fderiv ℝ p x (unitVector j)
  rw [hd.fderiv]
  change (fderiv ℝ p x (unitVector j) • unitVector (0 : Fin 3)) 0 =
    fderiv ℝ p x (unitVector j)
  simp [unitVector]

/-- Exact componentwise Fourier multiplier for an actual smooth periodic
scalar pressure gradient. -/
theorem datumFourierCoeff_gradient
    (p : Vec → ℝ) (hp : ContDiff ℝ ∞ p) (hperiod : SpatialPeriodic p) :
    datumFourierCoeff (SingularClosure.gradient p) =
      fun k i => derivativeSymbol i k * scalarPressureFourierCoeff p k := by
  funext k i
  have hcomponent (x : Vec) :
      SingularClosure.gradient p x i =
        coordinateDerivative (pressureAsFirstComponent p) i x 0 := by
    change fderiv ℝ p x (unitVector i) =
      coordinateDerivative (pressureAsFirstComponent p) i x 0
    exact (pressureAsFirstComponent_coordinateDerivative_zero p hp i x).symm
  have hbridge :
      datumFourierCoeff (SingularClosure.gradient p) k i =
        datumFourierCoeff (coordinateDerivative (pressureAsFirstComponent p) i) k 0 := by
    change (∫ x in unitCube,
      star (fourierCharacter k x) * (SingularClosure.gradient p x i : ℂ)) =
      ∫ x in unitCube, star (fourierCharacter k x) *
        (coordinateDerivative (pressureAsFirstComponent p) i x 0 : ℂ)
    apply integral_congr_ae
    refine Filter.Eventually.of_forall ?_
    intro x
    change star (fourierCharacter k x) * (SingularClosure.gradient p x i : ℂ) =
      star (fourierCharacter k x) *
        (coordinateDerivative (pressureAsFirstComponent p) i x 0 : ℂ)
    exact congrArg (fun r : ℝ => star (fourierCharacter k x) * (r : ℂ)) (hcomponent x)
  have hfourier := congrFun (congrFun
    (datumFourierCoeff_coordinateDerivative i (pressureAsFirstComponent p)
      (pressureAsFirstComponent_contDiff p hp)
      (pressureAsFirstComponent_periodic p hperiod)) k) (0 : Fin 3)
  change datumFourierCoeff (coordinateDerivative (pressureAsFirstComponent p) i) k 0 =
    derivativeSymbol i k * datumFourierCoeff (pressureAsFirstComponent p) k 0 at hfourier
  rw [datumFourierCoeff_pressureAsFirstComponent_zero] at hfourier
  exact hbridge.trans hfourier

/-- Every vector parallel to its integer frequency is annihilated by the
literal finite-dimensional Leray map, including frequency zero. -/
theorem coefficientLeray_frequency_mul_eq_zero (k : Frequency) (z : ℂ) :
    coefficientLeray k (fun i => (k i : ℂ) * z) = 0 := by
  funext i
  by_cases hk : k = 0
  · subst k
    simp [coefficientLeray]
  · have hden := frequency_complex_square_sum_ne_zero k hk
    simp only [coefficientLeray, hk, if_false, Pi.zero_apply]
    have hsum :
        (∑ j : Fin 3, (k j : ℂ) * ((k j : ℂ) * z)) =
          (∑ j : Fin 3, (k j : ℂ) ^ 2) * z := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    rw [hsum]
    field_simp [hden] <;> ring

theorem coefficientLeray_derivativeSymbol_mul_eq_zero (k : Frequency) (z : ℂ) :
    coefficientLeray k (fun i => derivativeSymbol i k * z) = 0 := by
  have hsymbol : (fun i => derivativeSymbol i k * z) =
      (fun i => (k i : ℂ) * ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) * z)) := by
    funext i
    simp only [derivativeSymbol, Complex.ofReal_mul, Complex.ofReal_intCast]
    ring
  rw [hsymbol]
  exact coefficientLeray_frequency_mul_eq_zero
    k ((((2 * Real.pi : ℝ) : ℂ) * Complex.I) * z)

/-- The actual Fourier coefficients of a smooth periodic pressure gradient
vanish after the actual modewise Leray projection. -/
theorem datumFourierCoeff_gradient_leray_eq_zero
    (p : Vec → ℝ) (hp : ContDiff ℝ ∞ p) (hperiod : SpatialPeriodic p)
    (k : Frequency) :
    coefficientLeray k (datumFourierCoeff (SingularClosure.gradient p) k) = 0 := by
  rw [datumFourierCoeff_gradient p hp hperiod]
  exact coefficientLeray_derivativeSymbol_mul_eq_zero k (scalarPressureFourierCoeff p k)

end

end MethbokeAddon.EhrenfestObstruction

