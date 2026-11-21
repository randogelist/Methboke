import QFAHeatSmoothing.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform NNReal Topology ContDiff

namespace QFAHeatSmoothing.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSemigroup
open MethbokeAddon.QuasiFeffermanA.HeatSmoothing
open MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

-- Physical carriers and the precise Fourier normalization.
example : MethbokeAddon.QuasiFeffermanA.Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

example (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatRate ξ = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 := rfl
example (ξ : MethbokeAddon.QuasiFeffermanA.Space) : 0 ≤ heatRate ξ := heatRate_nonneg ξ
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatRate ξ * heatValue ν t ξ ≤ ((ν : ℝ) * (t : ℝ))⁻¹ :=
  heatRate_mul_heatValue_le ν t hν ht ξ

example (ν t : ℝ≥0) (j k : Fin 3) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatHessianValue ν t j k ξ = -((2 * Real.pi) ^ 2) * ξ j * ξ k *
      Real.exp (-(4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ) * ‖ξ‖ ^ 2)) := rfl
example (ν t : ℝ≥0) (j k : Fin 3) : Continuous (heatHessianValue ν t j k) :=
  heatHessianValue_continuous ν t j k
example (ν t : ℝ≥0) (j k : Fin 3) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatHessianValue ν t j k (-ξ) = heatHessianValue ν t j k ξ :=
  heatHessianValue_even ν t j k ξ
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (j k : Fin 3) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    ‖heatHessianValue ν t j k ξ‖ ≤ ((ν : ℝ) * (t : ℝ))⁻¹ :=
  heatHessianValue_norm_le ν t hν ht j k ξ
example : (ν t : ℝ≥0) → 0 < ν → 0 < t → Fin 3 → Fin 3 → RealEvenSymbol :=
  heatHessianSymbol
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (j k : Fin 3) :
    (heatHessianSymbol ν t hν ht j k).bound = (ν * t)⁻¹ := rfl
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    (j k : Fin 3) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    (heatHessianSymbol ν t hν ht j k).value ξ = heatHessianValue ν t j k ξ := rfl

-- Every Hessian field is constructed as an actual real L2 Fourier multiplier.
example : (ν t : ℝ≥0) → 0 < ν → 0 < t → Fin 3 → Fin 3 → SpatialL2 → SpatialL2 :=
  heatHessianL2
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (j k : Fin 3) (v : SpatialL2) :
    heatHessianL2 ν t hν ht j k v =
      realFourierMultiplier (heatHessianSymbol ν t hν ht j k) v := rfl
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (j k : Fin 3) (v : SpatialL2) :
    (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
      (𝓕 (complexifyL2 (heatHessianL2 ν t hν ht j k v)) : ComplexL2) ξ) =ᵐ[volume]
        (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
          (heatHessianValue ν t j k ξ : ℂ) • (𝓕 (complexifyL2 v) : ComplexL2) ξ) :=
  heatHessianL2_fourier_ae ν t hν ht j k v
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (j k : Fin 3) (v : SpatialL2) :
    ‖heatHessianL2 ν t hν ht j k v‖ ≤ ((ν : ℝ) * (t : ℝ))⁻¹ * ‖v‖ :=
  norm_heatHessianL2_le ν t hν ht j k v

-- Both the packaged and literal compact-test weak Hessian conclusions are checked.
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (hG : SpatialWeakGradient v G) :
    SpatialWeakHessian (fun j => heatL2 ν t (G j))
      (fun j k => heatHessianL2 ν t hν ht j k v) :=
  spatialWeakHessian_heatL2 ν t hν ht hG
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t)
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (hG : SpatialWeakGradient v G) :
    ∀ j k : Fin 3, ∀ ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
        (∫ x : MethbokeAddon.QuasiFeffermanA.Space,
          fderiv ℝ ψ x (coordinateVector k) • heatL2 ν t (G j) x) =
          -(∫ x : MethbokeAddon.QuasiFeffermanA.Space,
            ψ x • heatHessianL2 ν t hν ht j k v x) :=
  spatialWeakHessian_heatL2 ν t hν ht hG

-- The output is the physical 13-component weak-derivative graph, not a spectral port.
example : (ν t : ℝ≥0) → 0 < ν → 0 < t → PhysicalH1 → PhysicalH2 := heatH1ToH2
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    heatH1ToH2 ν t hν ht u = physicalH2OfWeakDerivatives
      (heatL2 ν t (physicalH1Velocity u))
      (fun j => heatL2 ν t (physicalH1Gradient j u))
      (fun j k => heatHessianL2 ν t hν ht j k (physicalH1Velocity u))
      (spatialWeakGradient_heatL2 ν t (physicalH1_weakGradient u))
      (spatialWeakHessian_heatL2 ν t hν ht (physicalH1_weakGradient u)) := rfl
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    physicalH2Velocity (heatH1ToH2 ν t hν ht u) = heatL2 ν t (physicalH1Velocity u) :=
  heatH1ToH2_velocity ν t hν ht u
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) (j : Fin 3) :
    physicalH2Gradient j (heatH1ToH2 ν t hν ht u) =
      heatL2 ν t (physicalH1Gradient j u) := heatH1ToH2_gradient ν t hν ht u j
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) (j k : Fin 3) :
    physicalH2Hessian j k (heatH1ToH2 ν t hν ht u) =
      heatHessianL2 ν t hν ht j k (physicalH1Velocity u) :=
  heatH1ToH2_hessian ν t hν ht u j k
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    physicalH2ToH1 (heatH1ToH2 ν t hν ht u) = heatH1 ν t u := heatH1ToH2_toH1 ν t hν ht u

example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
      (𝓕 (complexifyL2 (physicalH2Laplacian (heatH1ToH2 ν t hν ht u))) : ComplexL2) ξ)
      =ᵐ[volume] (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
        ((-heatRate ξ * heatValue ν t ξ : ℝ) : ℂ) •
          (𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ) :=
  heatH1ToH2_laplacian_fourier_ae ν t hν ht u
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    ‖physicalH2Laplacian (heatH1ToH2 ν t hν ht u)‖ ^ 2 ≤
      ((ν : ℝ) * (t : ℝ))⁻¹ * physicalH1Enstrophy u :=
  heatH1ToH2_laplacian_norm_sq_le ν t hν ht u
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    ‖physicalH2Laplacian (heatH1ToH2 ν t hν ht u)‖ ^ 2 ≤
      ((ν : ℝ) * (t : ℝ))⁻¹ * (∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2) :=
  heatH1ToH2_laplacian_norm_sq_le ν t hν ht u
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    ‖heatH1ToH2 ν t hν ht u‖ ^ 2 ≤
      ‖u‖ ^ 2 + ((ν : ℝ) * (t : ℝ))⁻¹ * physicalH1Enstrophy u :=
  heatH1ToH2_norm_sq_le_energy_enstrophy ν t hν ht u
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    ‖heatH1ToH2 ν t hν ht u‖ ^ 2 ≤ (1 + ((ν : ℝ) * (t : ℝ))⁻¹) * ‖u‖ ^ 2 :=
  heatH1ToH2_norm_sq_le ν t hν ht u
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    ‖heatH1ToH2 ν t hν ht u‖ ≤ Real.sqrt (1 + ((ν : ℝ) * (t : ℝ))⁻¹) * ‖u‖ :=
  norm_heatH1ToH2_le ν t hν ht u
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u v : PhysicalH1) :
    heatH1ToH2 ν t hν ht (u + v) = heatH1ToH2 ν t hν ht u + heatH1ToH2 ν t hν ht v :=
  heatH1ToH2_add ν t hν ht u v
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (r : ℝ) (u : PhysicalH1) :
    heatH1ToH2 ν t hν ht (r • u) = r • heatH1ToH2 ν t hν ht u :=
  heatH1ToH2_smul ν t hν ht r u
example : (ν t : ℝ≥0) → 0 < ν → 0 < t → PhysicalH1 →L[ℝ] PhysicalH2 := heatH1ToH2CLM
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    heatH1ToH2CLM ν t hν ht u = heatH1ToH2 ν t hν ht u := heatH1ToH2CLM_apply ν t hν ht u

-- A separately assembled endpoint has no Hessian, spectral identity, or NSE premise.
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    ∃ w : PhysicalH2,
      physicalH2Velocity w = heatL2 ν t (physicalH1Velocity u) ∧
      physicalH2ToH1 w = heatH1 ν t u ∧
      ‖physicalH2Laplacian w‖ ^ 2 ≤
        ((ν : ℝ) * (t : ℝ))⁻¹ * (∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2) :=
  ⟨heatH1ToH2 ν t hν ht u, heatH1ToH2_velocity ν t hν ht u,
    heatH1ToH2_toH1 ν t hν ht u, heatH1ToH2_laplacian_norm_sq_le ν t hν ht u⟩

end QFAHeatSmoothing.ExpectedTypes

-- Ordered named type and axiom evidence follows.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_nonneg"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_nonneg"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_mul_heatValue_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_mul_heatValue_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_mul_heatValue_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_mul_heatValue_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_mul_heatValue_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatRate_mul_heatValue_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_continuous"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_even"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_even
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_even"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_even"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_even
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_even"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_norm_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_norm_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_norm_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_norm_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_norm_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianValue_norm_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianSymbol"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianSymbol
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianSymbol"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatHessianL2_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatHessianL2_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatHessianL2_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatHessianL2_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatHessianL2_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatHessianL2_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatHessianL2_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.spatialWeakHessian_heatL2"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.spatialWeakHessian_heatL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.spatialWeakHessian_heatL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.spatialWeakHessian_heatL2"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.spatialWeakHessian_heatL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.spatialWeakHessian_heatL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_velocity"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_gradient"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_hessian"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_hessian
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_hessian"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_hessian"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_hessian
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_hessian"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_toH1"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_toH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_toH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_toH1"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_toH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_toH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_norm_sq_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_norm_sq_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_laplacian_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le_energy_enstrophy"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le_energy_enstrophy
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le_energy_enstrophy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le_energy_enstrophy"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le_energy_enstrophy
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le_energy_enstrophy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatH1ToH2_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatH1ToH2_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatH1ToH2_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatH1ToH2_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatH1ToH2_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.norm_heatH1ToH2_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_add"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_add"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_smul"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSmoothing.heatH1ToH2CLM_apply"
