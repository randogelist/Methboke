import R3EhrenfestSharpCutoff.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ContDiff NNReal

namespace R3EhrenfestSharpCutoff.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers
open MethbokeAddon.QuasiFeffermanA.RealFourier
open MethbokeAddon.QuasiFeffermanA.LerayMultiplier
open MethbokeAddon.QuasiFeffermanA.LerayH1
open MethbokeAddon.R3Ehrenfest.SharpCutoff
open QFA.Endpoints.Representation
open QFA.Endpoints.Agmon (ComplexVector ComplexL2)

-- Domain and measure are the original whole-space real and complex L2 objects.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

-- The symbol is the actual closed-ball characteristic function at radius n+1.
example (n : ℕ) : cutoffRadius n = (n : ℝ) + 1 := rfl
example (n : ℕ) : 0 < cutoffRadius n := cutoffRadius_pos n
example (n : ℕ) (ξ : Space) :
    cutoffValue n ξ = if ‖ξ‖ ≤ (n : ℝ) + 1 then 1 else 0 := rfl
example (n : ℕ) : Measurable (cutoffValue n) := measurable_cutoffValue n
example (n : ℕ) (ξ : Space) : cutoffValue n (-ξ) = cutoffValue n ξ :=
  cutoffValue_neg n ξ
example (n : ℕ) (ξ : Space) : ‖cutoffValue n ξ‖ ≤ 1 := norm_cutoffValue_le n ξ
example (n : ℕ) (ξ : Space) :
    cutoffValue n ξ * cutoffValue n ξ = cutoffValue n ξ := cutoffValue_mul_self n ξ
example (n : ℕ) : RealEvenSymbol := cutoffSymbol n
example (n : ℕ) : (cutoffSymbol n).value = cutoffValue n := rfl
example (n : ℕ) : (cutoffSymbol n).bound = 1 := rfl

-- The multiplier is the existing actual inverse-Fourier construction.
example (n : ℕ) : SpatialL2 →L[ℝ] SpatialL2 := sharpCutoff n
example (n : ℕ) (u : SpatialL2) :
    sharpCutoff n u = realFourierMultiplier (cutoffSymbol n) u := sharpCutoff_apply n u
example (n : ℕ) (u : SpatialL2) :
    sharpCutoff n u = realPartL2CLM
      (𝓕⁻ (frequencyMultiplier (cutoffSymbol n) (𝓕 (complexifyL2 u)))) := rfl
example (n : ℕ) (u : SpatialL2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space =>
        ((if ‖ξ‖ ≤ (n : ℝ) + 1 then 1 else 0 : ℝ) : ℂ) •
          (𝓕 (complexifyL2 u) : ComplexL2) ξ) := sharpCutoff_fourier_ae n u
example (n : ℕ) (u : SpatialL2) :
    ∀ᵐ ξ : Space ∂volume, (n : ℝ) + 1 < ‖ξ‖ →
      (𝓕 (complexifyL2 (sharpCutoff n u)) : ComplexL2) ξ = 0 :=
  sharpCutoff_fourier_outside n u
example (n : ℕ) (u : SpatialL2) : ‖sharpCutoff n u‖ ≤ ‖u‖ := norm_sharpCutoff_le n u
example (n : ℕ) (u : SpatialL2) :
    sharpCutoff n (sharpCutoff n u) = sharpCutoff n u := sharpCutoff_idempotent n u
example (n : ℕ) (u v : SpatialL2) :
    inner ℝ (sharpCutoff n u) v = inner ℝ u (sharpCutoff n v) :=
  inner_sharpCutoff_left n u v
example (n : ℕ) (u : SpatialL2) :
    sharpCutoff n (realLeray u) = realLeray (sharpCutoff n u) := sharpCutoff_realLeray n u
example (n : ℕ) (u : SpatialL2) (hu : Solenoidal u) : Solenoidal (sharpCutoff n u) :=
  solenoidal_sharpCutoff n u hu

-- Native compact-test weak gradients, expanded independently.
example (n : ℕ) (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (h : ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • v x) =
        -(∫ x : Space, ψ x • G j x)) :
    ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) •
        sharpCutoff n v x) =
          -(∫ x : Space, ψ x • sharpCutoff n (G j) x) :=
  spatialWeakGradient_sharpCutoff n h

-- This is a lift on the existing physical graph, not a redefined H1 carrier.
example (n : ℕ) (u : PhysicalH1) : PhysicalH1 := physicalH1SharpCutoff n u
example (n : ℕ) (u : PhysicalH1) :
    physicalH1SharpCutoff n u =
      physicalH1OfWeakGradient (sharpCutoff n (physicalH1Velocity u))
        (fun j => sharpCutoff n (physicalH1Gradient j u))
        (spatialWeakGradient_sharpCutoff n (physicalH1_weakGradient u)) := rfl
example (n : ℕ) (u : PhysicalH1) :
    physicalH1Velocity (physicalH1SharpCutoff n u) = sharpCutoff n (physicalH1Velocity u) :=
  physicalH1SharpCutoff_velocity n u
example (n : ℕ) (u : PhysicalH1) (j : Fin 3) :
    physicalH1Gradient j (physicalH1SharpCutoff n u) = sharpCutoff n (physicalH1Gradient j u) :=
  physicalH1SharpCutoff_gradient n u j
example (n : ℕ) (u : PhysicalH1) :
    ‖physicalH1SharpCutoff n u‖ ^ 2 ≤ ‖u‖ ^ 2 := physicalH1SharpCutoff_norm_sq_le n u
example (n : ℕ) (u : PhysicalH1) :
    ‖physicalH1SharpCutoff n u‖ ≤ ‖u‖ := norm_physicalH1SharpCutoff_le n u
example (n : ℕ) : PhysicalH1 →L[ℝ] PhysicalH1 := physicalH1SharpCutoffCLM n
example (n : ℕ) (u : PhysicalH1) :
    physicalH1SharpCutoffCLM n u = physicalH1SharpCutoff n u := physicalH1SharpCutoffCLM_apply n u
example (n : ℕ) (u : PhysicalH1) :
    physicalH1SharpCutoff n (physicalH1SharpCutoff n u) = physicalH1SharpCutoff n u :=
  physicalH1SharpCutoff_idempotent n u
example (n : ℕ) (u v : PhysicalH1) :
    inner ℝ (physicalH1SharpCutoff n u) v = inner ℝ u (physicalH1SharpCutoff n v) :=
  inner_physicalH1SharpCutoff_left n u v
example (n : ℕ) (u : PhysicalH1) :
    physicalH1SharpCutoff n (physicalH1Leray u) =
      physicalH1Leray (physicalH1SharpCutoff n u) := physicalH1SharpCutoff_physicalH1Leray n u

end R3EhrenfestSharpCutoff.ExpectedTypes

-- Ordered exact-type and named axiom reports, executed only by authorized external CI.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius_pos"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius_pos
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius_pos"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffRadius_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.measurable_cutoffValue"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.measurable_cutoffValue
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.measurable_cutoffValue"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.measurable_cutoffValue"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.measurable_cutoffValue
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.measurable_cutoffValue"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_neg"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_neg
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_neg"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_cutoffValue_le"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_cutoffValue_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_cutoffValue_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_cutoffValue_le"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_cutoffValue_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_cutoffValue_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_mul_self"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_mul_self
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_mul_self"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_mul_self"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_mul_self
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffValue_mul_self"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffSymbol"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffSymbol
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffSymbol"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.cutoffSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_apply"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_apply
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_apply"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_ae"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_ae"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_outside"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_outside
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_outside"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_outside"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_outside
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_fourier_outside"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_sharpCutoff_le"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_sharpCutoff_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_sharpCutoff_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_sharpCutoff_le"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_sharpCutoff_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_sharpCutoff_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_idempotent"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_idempotent"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_sharpCutoff_left"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_sharpCutoff_left
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_sharpCutoff_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_sharpCutoff_left"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_sharpCutoff_left
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_sharpCutoff_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_realLeray"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_realLeray
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_realLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_realLeray"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_realLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.sharpCutoff_realLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.solenoidal_sharpCutoff"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.solenoidal_sharpCutoff
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.solenoidal_sharpCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.solenoidal_sharpCutoff"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.solenoidal_sharpCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.solenoidal_sharpCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.spatialWeakGradient_sharpCutoff"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.spatialWeakGradient_sharpCutoff
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.spatialWeakGradient_sharpCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.spatialWeakGradient_sharpCutoff"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.spatialWeakGradient_sharpCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.spatialWeakGradient_sharpCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_velocity"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_velocity
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_velocity"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_gradient"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_gradient
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_gradient"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_norm_sq_le"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_norm_sq_le"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_physicalH1SharpCutoff_le"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_physicalH1SharpCutoff_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_physicalH1SharpCutoff_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_physicalH1SharpCutoff_le"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_physicalH1SharpCutoff_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.norm_physicalH1SharpCutoff_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM_apply"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM_apply"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoffCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_idempotent"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_idempotent"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_physicalH1SharpCutoff_left"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_physicalH1SharpCutoff_left
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_physicalH1SharpCutoff_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_physicalH1SharpCutoff_left"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_physicalH1SharpCutoff_left
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.inner_physicalH1SharpCutoff_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_physicalH1Leray"
#check @MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_physicalH1Leray
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_physicalH1Leray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_physicalH1Leray"
#print axioms MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_physicalH1Leray
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SharpCutoff.physicalH1SharpCutoff_physicalH1Leray"

