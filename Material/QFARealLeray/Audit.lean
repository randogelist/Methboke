import QFARealLeray.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators ContDiff SchwartzMap LineDeriv FourierTransform

namespace QFARealLeray.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.LerayMultiplier
open MethbokeAddon.QuasiFeffermanA.LerayH1
open MethbokeAddon.QuasiFeffermanA.LeraySolenoidal
open MethbokeAddon.QuasiFeffermanA.RealFourier
open MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers
open MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers
open MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

-- Literal full-volume physical carriers and original native graph predicates.
example : MethbokeAddon.QuasiFeffermanA.Space = EuclideanSpace ℝ (Fin 3) := rfl
example : ComplexVector = EuclideanSpace ℂ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : PhysicalH1 = physicalH1Graph.toSubmodule := rfl
example : PhysicalH1Sigma = physicalH1SigmaGraph.toSubmodule := rfl

-- The frequency symbol is a constructed orthogonal projection, including zero.
example (ξ : EuclideanSpace ℝ (Fin 3)) :
    leraySymbol ξ = (Submodule.span ℂ {complexifyVectorLI ξ}).orthogonal.starProjection := rfl
example (v : SpatialL2) :
    realLeray v = realPartL2CLM
      (𝓕⁻ (frequencyLeray (𝓕 (complexifyL2 v)))) := rfl

-- Actual graph membership and the unique projected weak derivatives are retained.
example (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : ∀ (j : Fin 3) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : EuclideanSpace ℝ (Fin 3),
          fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • v x) =
          -(∫ x : EuclideanSpace ℝ (Fin 3), ψ x • G j x)) :
    ∀ (j : Fin 3) (ψ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : EuclideanSpace ℝ (Fin 3),
          fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • realLeray v x) =
          -(∫ x : EuclideanSpace ℝ (Fin 3), ψ x • realLeray (G j) x) :=
  spatialWeakGradient_realLeray h
example (u : PhysicalH1) :
    (physicalH1Leray u).val = WithLp.toLp 2
      (Fin.cons (realLeray (physicalH1Velocity u))
        (fun j => realLeray (physicalH1Gradient j u))) := rfl
example (u : PhysicalH1) :
    (physicalH1SigmaLeray u).val = WithLp.toLp 2
      (Fin.cons (realLeray (physicalH1Velocity u))
        (fun j => realLeray (physicalH1Gradient j u))) := rfl

-- Full all-L2 native range, with every compact scalar test and integrability.
example (v : Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    (∃ w : Lp (EuclideanSpace ℝ (Fin 3)) 2
      (volume : Measure (EuclideanSpace ℝ (Fin 3))), realLeray w = v) ↔
    ∀ (ψ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        Integrable (fun x : EuclideanSpace ℝ (Fin 3) => inner ℝ (v x)
          (WithLp.toLp 2 (fun j : Fin 3 =>
            fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))))) volume ∧
        (∫ x : EuclideanSpace ℝ (Fin 3), inner ℝ (v x)
          (WithLp.toLp 2 (fun j : Fin 3 =>
            fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))))) = 0 :=
  realLeray_range_iff_solenoidal v

-- Native H1 fixed points are precisely the original solenoidal graph velocities.
example (u : PhysicalH1) : physicalH1Leray u = u ↔
    ∀ (ψ : EuclideanSpace ℝ (Fin 3) → ℝ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
          inner ℝ (physicalH1Velocity u x) (scalarGradient ψ x)) volume ∧
        (∫ x : EuclideanSpace ℝ (Fin 3),
          inner ℝ (physicalH1Velocity u x) (scalarGradient ψ x)) = 0 :=
  physicalH1Leray_eq_self_iff u

-- Independently stated full expected types for every registered public name.

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space),
    ComplexVector →L[ℂ] ComplexVector :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_formula
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space) (z : ComplexVector),
    leraySymbol ξ z = z -
      (inner ℂ (complexifyVectorLI ξ) z / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • complexifyVectorLI ξ :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_formula

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_complexifyVector_eq_sum
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space) (z : ComplexVector),
    inner ℂ (complexifyVectorLI ξ) z =
      ∑ j : Fin 3, (ξ j : ℂ) * z j :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_complexifyVector_eq_sum

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_coordinate
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space) (z : ComplexVector) (j : Fin 3),
    leraySymbol ξ z j = z j -
      ((∑ k : Fin 3, (ξ k : ℂ) * z k) / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) * (ξ j : ℂ) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_coordinate

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_zero
example : ∀ (z : ComplexVector),
    leraySymbol 0 z = z :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_zero

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_leraySymbol_le
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space) (z : ComplexVector),
    ‖leraySymbol ξ z‖ ≤ ‖z‖ :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_leraySymbol_le

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_leraySymbol_left
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space) (z w : ComplexVector),
    inner ℂ (leraySymbol ξ z) w = inner ℂ z (leraySymbol ξ w) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_leraySymbol_left

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_idempotent
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space) (z : ComplexVector),
    leraySymbol ξ (leraySymbol ξ z) = leraySymbol ξ z :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_idempotent

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_eq_self_iff
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space) (z : ComplexVector),
    leraySymbol ξ z = z ↔ inner ℂ (complexifyVectorLI ξ) z = 0 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_eq_self_iff

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_transverse
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space) (z : ComplexVector),
    inner ℂ (complexifyVectorLI ξ) (leraySymbol ξ z) = 0 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_transverse

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_neg
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space),
    leraySymbol (-ξ) = leraySymbol ξ :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_neg

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.conjugate_leraySymbol
example : ∀ (ξ : MethbokeAddon.QuasiFeffermanA.Space) (z : ComplexVector),
    conjugateVectorLI (leraySymbol ξ z) =
      leraySymbol ξ (conjugateVectorLI z) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.conjugate_leraySymbol

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray
example : ∀ (f : ComplexL2),
    ComplexL2 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_ae
example : ∀ (f : ComplexL2),
    (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => frequencyLeray f ξ) =ᵐ[volume]
      (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => leraySymbol ξ (f ξ)) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_ae

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_frequencyLeray_le
example : ∀ (f : ComplexL2),
    ‖frequencyLeray f‖ ≤ ‖f‖ :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_frequencyLeray_le

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM
example : ComplexL2 →L[ℂ] ComplexL2 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM_apply
example : ∀ (f : ComplexL2),
    frequencyLerayCLM f = frequencyLeray f :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM_apply

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_idempotent
example : ∀ (f : ComplexL2),
    frequencyLeray (frequencyLeray f) = frequencyLeray f :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_idempotent

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_frequencyLeray_left
example : ∀ (f g : ComplexL2),
    inner ℂ (frequencyLeray f) g = inner ℂ f (frequencyLeray g) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_frequencyLeray_left

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_multiplier_ae
example : ∀ (f g : ComplexL2) (m : MethbokeAddon.QuasiFeffermanA.Space → ℂ)
    (h : (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => g ξ) =ᵐ[volume] (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => m ξ • f ξ)),
    (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => frequencyLeray g ξ) =ᵐ[volume]
      (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => m ξ • frequencyLeray f ξ) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_multiplier_ae

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_frequencySector
example : ∀ (i : Fin 6) (f : ComplexL2),
    frequencyLeray (frequencySector i f) = frequencySector i (frequencyLeray f) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_frequencySector

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.hermitian_frequencyLeray
example : ∀ (f : ComplexL2),
    hermitianL2CLM (frequencyLeray f) = frequencyLeray (hermitianL2CLM f) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.hermitian_frequencyLeray

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray
example : ∀ (f : ComplexL2),
    ComplexL2 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourier_fourierLeray
example : ∀ (f : ComplexL2),
    𝓕 (fourierLeray f) = frequencyLeray (𝓕 f) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourier_fourierLeray

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM
example : ComplexL2 →L[ℂ] ComplexL2 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM_apply
example : ∀ (f : ComplexL2),
    fourierLerayCLM f = fourierLeray f :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM_apply

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_fourierLeray_le
example : ∀ (f : ComplexL2),
    ‖fourierLeray f‖ ≤ ‖f‖ :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_fourierLeray_le

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_idempotent
example : ∀ (f : ComplexL2),
    fourierLeray (fourierLeray f) = fourierLeray f :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_idempotent

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_fourierLeray_left
example : ∀ (f g : ComplexL2),
    inner ℂ (fourierLeray f) g = inner ℂ f (fourierLeray g) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_fourierLeray_left

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_fourierSector
example : ∀ (i : Fin 6) (f : ComplexL2),
    fourierLeray (fourierSector i f) = fourierSector i (fourierLeray f) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_fourierSector

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray
example : ∀ (v : SpatialL2),
    SpatialL2 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.complexify_realLeray
example : ∀ (v : SpatialL2),
    complexifyL2 (realLeray v) = fourierLeray (complexifyL2 v) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.complexify_realLeray

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM
example : SpatialL2 →L[ℝ] SpatialL2 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM_apply
example : ∀ (v : SpatialL2),
    realLerayCLM v = realLeray v :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM_apply

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_realLeray_le
example : ∀ (v : SpatialL2),
    ‖realLeray v‖ ≤ ‖v‖ :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_realLeray_le

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_idempotent
example : ∀ (v : SpatialL2),
    realLeray (realLeray v) = realLeray v :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_idempotent

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_realLeray_left
example : ∀ (u v : SpatialL2),
    inner ℝ (realLeray u) v = inner ℝ u (realLeray v) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_realLeray_left

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_orthogonal_complement
example : ∀ (u v : SpatialL2),
    inner ℝ (realLeray u) (v - realLeray v) = 0 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_orthogonal_complement

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_norm_sq_split
example : ∀ (v : SpatialL2),
    ‖v‖ ^ 2 = ‖realLeray v‖ ^ 2 + ‖v - realLeray v‖ ^ 2 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_norm_sq_split

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_ae
example : ∀ (v : SpatialL2),
    (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => (𝓕 (complexifyL2 (realLeray v)) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => leraySymbol ξ ((𝓕 (complexifyL2 v) : ComplexL2) ξ)) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_ae

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_transverse
example : ∀ (v : SpatialL2),
    ∀ᵐ ξ : MethbokeAddon.QuasiFeffermanA.Space ∂volume,
      inner ℂ (complexifyVectorLI ξ)
        ((𝓕 (complexifyL2 (realLeray v)) : ComplexL2) ξ) = 0 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_transverse

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_eq_self_iff_fourier_transverse
example : ∀ (v : SpatialL2),
    realLeray v = v ↔ ∀ᵐ ξ : MethbokeAddon.QuasiFeffermanA.Space ∂volume,
      inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ) = 0 :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_eq_self_iff_fourier_transverse

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_realFourierSector
example : ∀ (i : Fin 6) (v : SpatialL2),
    realLeray (realFourierSector i v) = realFourierSector i (realLeray v) :=
  @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_realFourierSector

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_realLeray
example : ∀ {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G),
    SpatialWeakGradient (realLeray v) (fun j => realLeray (G j)) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_realLeray

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialGradientTrace_fourier_ae
example : ∀ {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G),
    (fun ξ : MethbokeAddon.QuasiFeffermanA.Space => (𝓕 (complexifyL2 (spatialGradientTrace G)) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
        ((2 * Real.pi * Complex.I) *
          inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ)) •
            EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.spatialGradientTrace_fourier_ae

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_solenoidal_iff_fourier_transverse
example : ∀ {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G),
    Solenoidal v ↔ ∀ᵐ ξ : MethbokeAddon.QuasiFeffermanA.Space ∂volume,
      inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ) = 0 :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_solenoidal_iff_fourier_transverse

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray_of_weakGradient
example : ∀ {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G),
    Solenoidal (realLeray v) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray_of_weakGradient

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.realLeray_eq_self_of_solenoidal
example : ∀ {v : SpatialL2} {G : Fin 3 → SpatialL2}
    (h : SpatialWeakGradient v G) (hs : Solenoidal v),
    realLeray v = v :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.realLeray_eq_self_of_solenoidal

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray
example : ∀ (v : SpatialL2),
    Solenoidal (realLeray v) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray
example : ∀ (u : PhysicalH1),
    PhysicalH1 :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_velocity
example : ∀ (u : PhysicalH1),
    physicalH1Velocity (physicalH1Leray u) = realLeray (physicalH1Velocity u) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_velocity

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_gradient
example : ∀ (u : PhysicalH1) (j : Fin 3),
    physicalH1Gradient j (physicalH1Leray u) = realLeray (physicalH1Gradient j u) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_gradient

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_le
example : ∀ (u : PhysicalH1),
    ‖physicalH1Leray u‖ ^ 2 ≤ ‖u‖ ^ 2 :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_le

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.norm_physicalH1Leray_le
example : ∀ (u : PhysicalH1),
    ‖physicalH1Leray u‖ ≤ ‖u‖ :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.norm_physicalH1Leray_le

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM
example : PhysicalH1 →L[ℝ] PhysicalH1 :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM_apply
example : ∀ (u : PhysicalH1),
    physicalH1LerayCLM u = physicalH1Leray u :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM_apply

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_idempotent
example : ∀ (u : PhysicalH1),
    physicalH1Leray (physicalH1Leray u) = physicalH1Leray u :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_idempotent

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.inner_physicalH1Leray_left
example : ∀ (u v : PhysicalH1),
    inner ℝ (physicalH1Leray u) v = inner ℝ u (physicalH1Leray v) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.inner_physicalH1Leray_left

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_orthogonal_complement
example : ∀ (u v : PhysicalH1),
    inner ℝ (physicalH1Leray u) (v - physicalH1Leray v) = 0 :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_orthogonal_complement

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_split
example : ∀ (u : PhysicalH1),
    ‖u‖ ^ 2 = ‖physicalH1Leray u‖ ^ 2 + ‖u - physicalH1Leray u‖ ^ 2 :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_split

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_solenoidal
example : ∀ (u : PhysicalH1),
    Solenoidal (physicalH1Velocity (physicalH1Leray u)) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_solenoidal

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_eq_self_iff
example : ∀ (u : PhysicalH1),
    physicalH1Leray u = u ↔ Solenoidal (physicalH1Velocity u) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_eq_self_iff

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_range_iff
example : ∀ (u : PhysicalH1),
    (∃ w : PhysicalH1, physicalH1Leray w = u) ↔ Solenoidal (physicalH1Velocity u) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_range_iff

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray
example : ∀ (u : PhysicalH1),
    PhysicalH1Sigma :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray_toH1
example : ∀ (u : PhysicalH1),
    physicalH1SigmaToH1LI (physicalH1SigmaLeray u) = physicalH1Leray u :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray_toH1

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sigma_identity
example : ∀ (u : PhysicalH1Sigma),
    physicalH1Leray (physicalH1SigmaToH1LI u) = physicalH1SigmaToH1LI u :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sigma_identity

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sector
example : ∀ (i : Fin 6) (u : PhysicalH1),
    physicalH1Leray (physicalH1Sector i u) = physicalH1Sector i (physicalH1Leray u) :=
  @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sector

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_fourier_transverse
example : ∀ {v : SpatialL2} (hsol : Solenoidal v),
    ∀ᵐ ξ : MethbokeAddon.QuasiFeffermanA.Space ∂volume,
      inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ) = 0 :=
  @MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_fourier_transverse

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_iff_fourier_transverse
example : ∀ (v : SpatialL2),
    Solenoidal v ↔ ∀ᵐ ξ : MethbokeAddon.QuasiFeffermanA.Space ∂volume,
      inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ) = 0 :=
  @MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_iff_fourier_transverse

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_eq_self_iff_solenoidal
example : ∀ (v : SpatialL2),
    realLeray v = v ↔ Solenoidal v :=
  @MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_eq_self_iff_solenoidal

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_range_iff_solenoidal
example : ∀ (v : SpatialL2),
    (∃ w : SpatialL2, realLeray w = v) ↔ Solenoidal v :=
  @MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_range_iff_solenoidal

-- FULL_CONSUMER:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_realFourierSector_L2
example : ∀ (i : Fin 6)
    {v : SpatialL2} (hsol : Solenoidal v),
    Solenoidal (realFourierSector i v) :=
  @MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_realFourierSector_L2

end QFARealLeray.ExpectedTypes

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_formula"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_formula
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_formula"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_formula"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_formula
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_formula"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_complexifyVector_eq_sum"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_complexifyVector_eq_sum
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_complexifyVector_eq_sum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_complexifyVector_eq_sum"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_complexifyVector_eq_sum
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_complexifyVector_eq_sum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_coordinate"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_coordinate
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_coordinate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_coordinate"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_coordinate
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_coordinate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_zero"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_leraySymbol_le"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_leraySymbol_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_leraySymbol_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_leraySymbol_le"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_leraySymbol_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_leraySymbol_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_leraySymbol_left"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_leraySymbol_left
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_leraySymbol_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_leraySymbol_left"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_leraySymbol_left
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_leraySymbol_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_idempotent"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_idempotent"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_eq_self_iff"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_eq_self_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_eq_self_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_eq_self_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_eq_self_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_eq_self_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_transverse"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_transverse
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_transverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_transverse"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_transverse
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_transverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_neg"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_neg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_neg"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.leraySymbol_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.conjugate_leraySymbol"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.conjugate_leraySymbol
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.conjugate_leraySymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.conjugate_leraySymbol"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.conjugate_leraySymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.conjugate_leraySymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_ae"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_frequencyLeray_le"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_frequencyLeray_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_frequencyLeray_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_frequencyLeray_le"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_frequencyLeray_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_frequencyLeray_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLerayCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_idempotent"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_idempotent"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_frequencyLeray_left"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_frequencyLeray_left
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_frequencyLeray_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_frequencyLeray_left"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_frequencyLeray_left
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_frequencyLeray_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_multiplier_ae"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_multiplier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_multiplier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_multiplier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_multiplier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_multiplier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_frequencySector"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_frequencySector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_frequencySector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_frequencySector"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_frequencySector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.frequencyLeray_frequencySector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.hermitian_frequencyLeray"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.hermitian_frequencyLeray
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.hermitian_frequencyLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.hermitian_frequencyLeray"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.hermitian_frequencyLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.hermitian_frequencyLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourier_fourierLeray"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourier_fourierLeray
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourier_fourierLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourier_fourierLeray"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourier_fourierLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourier_fourierLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLerayCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_fourierLeray_le"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_fourierLeray_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_fourierLeray_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_fourierLeray_le"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_fourierLeray_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_fourierLeray_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_idempotent"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_idempotent"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_fourierLeray_left"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_fourierLeray_left
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_fourierLeray_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_fourierLeray_left"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_fourierLeray_left
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_fourierLeray_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_fourierSector"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_fourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_fourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_fourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_fourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.fourierLeray_fourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.complexify_realLeray"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.complexify_realLeray
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.complexify_realLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.complexify_realLeray"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.complexify_realLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.complexify_realLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLerayCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_realLeray_le"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_realLeray_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_realLeray_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_realLeray_le"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_realLeray_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.norm_realLeray_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_idempotent"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_idempotent"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_realLeray_left"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_realLeray_left
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_realLeray_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_realLeray_left"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_realLeray_left
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.inner_realLeray_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_orthogonal_complement"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_orthogonal_complement
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_orthogonal_complement"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_orthogonal_complement"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_orthogonal_complement
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_orthogonal_complement"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_norm_sq_split"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_norm_sq_split
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_norm_sq_split"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_norm_sq_split"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_norm_sq_split
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_norm_sq_split"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_transverse"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_transverse
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_transverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_transverse"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_transverse
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_fourier_transverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_eq_self_iff_fourier_transverse"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_eq_self_iff_fourier_transverse
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_eq_self_iff_fourier_transverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_eq_self_iff_fourier_transverse"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_eq_self_iff_fourier_transverse
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_eq_self_iff_fourier_transverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_realFourierSector"
#check @MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_realFourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_realFourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_realFourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_realFourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayMultiplier.realLeray_realFourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_realLeray"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_realLeray
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_realLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_realLeray"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_realLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_realLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialGradientTrace_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.spatialGradientTrace_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialGradientTrace_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialGradientTrace_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.spatialGradientTrace_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialGradientTrace_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_solenoidal_iff_fourier_transverse"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_solenoidal_iff_fourier_transverse
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_solenoidal_iff_fourier_transverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_solenoidal_iff_fourier_transverse"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_solenoidal_iff_fourier_transverse
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.spatialWeakGradient_solenoidal_iff_fourier_transverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray_of_weakGradient"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray_of_weakGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray_of_weakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray_of_weakGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray_of_weakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray_of_weakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.realLeray_eq_self_of_solenoidal"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.realLeray_eq_self_of_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.realLeray_eq_self_of_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.realLeray_eq_self_of_solenoidal"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.realLeray_eq_self_of_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.realLeray_eq_self_of_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.solenoidal_realLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_velocity"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_gradient"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_le"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_le"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.norm_physicalH1Leray_le"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.norm_physicalH1Leray_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.norm_physicalH1Leray_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.norm_physicalH1Leray_le"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.norm_physicalH1Leray_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.norm_physicalH1Leray_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1LerayCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_idempotent"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_idempotent"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.inner_physicalH1Leray_left"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.inner_physicalH1Leray_left
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.inner_physicalH1Leray_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.inner_physicalH1Leray_left"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.inner_physicalH1Leray_left
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.inner_physicalH1Leray_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_orthogonal_complement"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_orthogonal_complement
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_orthogonal_complement"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_orthogonal_complement"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_orthogonal_complement
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_orthogonal_complement"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_split"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_split
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_split"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_split"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_split
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_norm_sq_split"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_solenoidal"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_solenoidal"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_eq_self_iff"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_eq_self_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_eq_self_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_eq_self_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_eq_self_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_eq_self_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_range_iff"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_range_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_range_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_range_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_range_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_range_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray_toH1"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray_toH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray_toH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray_toH1"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray_toH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1SigmaLeray_toH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sigma_identity"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sigma_identity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sigma_identity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sigma_identity"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sigma_identity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sigma_identity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sector"
#check @MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sector"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayH1.physicalH1Leray_sector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_fourier_transverse"
#check @MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_fourier_transverse
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_fourier_transverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_fourier_transverse"
#print axioms MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_fourier_transverse
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_fourier_transverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_iff_fourier_transverse"
#check @MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_iff_fourier_transverse
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_iff_fourier_transverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_iff_fourier_transverse"
#print axioms MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_iff_fourier_transverse
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_iff_fourier_transverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_eq_self_iff_solenoidal"
#check @MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_eq_self_iff_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_eq_self_iff_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_eq_self_iff_solenoidal"
#print axioms MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_eq_self_iff_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_eq_self_iff_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_range_iff_solenoidal"
#check @MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_range_iff_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_range_iff_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_range_iff_solenoidal"
#print axioms MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_range_iff_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.realLeray_range_iff_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_realFourierSector_L2"
#check @MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_realFourierSector_L2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_realFourierSector_L2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_realFourierSector_L2"
#print axioms MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_realFourierSector_L2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LeraySolenoidal.solenoidal_realFourierSector_L2"

