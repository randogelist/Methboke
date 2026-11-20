import QFAHeatSemigroup.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform NNReal Topology

namespace QFAHeatSemigroup.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSemigroup
open MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers
open MethbokeAddon.QuasiFeffermanA.RealFourier
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

-- The spatial fibers and L2 carrier are literal full-volume Euclidean ones.
example : MethbokeAddon.QuasiFeffermanA.Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

-- Literal symbol, actual nonnegative parameter domains and elementary laws.
example : ℝ≥0 → ℝ≥0 → MethbokeAddon.QuasiFeffermanA.Space → ℝ := heatValue
example (ν t : ℝ≥0) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatValue ν t ξ = Real.exp (-(4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ) * ‖ξ‖ ^ 2)) := rfl
example (ν t : ℝ≥0) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    0 < heatValue ν t ξ := heatValue_pos ν t ξ
example (ν t : ℝ≥0) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatValue ν t ξ ≤ 1 := heatValue_le_one ν t ξ
example (ν t : ℝ≥0) : Continuous (heatValue ν t) := heatValue_continuous_frequency ν t
example (ν : ℝ≥0) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    Continuous (fun t : ℝ≥0 => heatValue ν t ξ) := heatValue_continuous_time ν ξ
example (ν t : ℝ≥0) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatValue ν t (-ξ) = heatValue ν t ξ := heatValue_neg ν t ξ
example (ν : ℝ≥0) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatValue ν 0 ξ = 1 := heatValue_zero_time ν ξ
example (t : ℝ≥0) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatValue 0 t ξ = 1 := heatValue_zero_viscosity t ξ
example (ν s t : ℝ≥0) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatValue ν (s + t) ξ = heatValue ν s ξ * heatValue ν t ξ :=
  heatValue_add_time ν s t ξ
example : ℝ≥0 → ℝ≥0 → RealEvenSymbol := heatSymbol
example (ν t : ℝ≥0) : (heatSymbol ν t).bound = (1 : ℝ≥0) := rfl
example (ν t : ℝ≥0) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    (heatSymbol ν t).value ξ =
      Real.exp (-(4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ) * ‖ξ‖ ^ 2)) :=
  heatSymbol_value ν t ξ

-- Constructed real L2 operator, its literal inverse-Fourier formula and full laws.
example : ℝ≥0 → ℝ≥0 → SpatialL2 → SpatialL2 := heatL2
example (ν t : ℝ≥0) (u : SpatialL2) :
    heatL2 ν t u = realPartL2CLM
      (𝓕⁻ (frequencyMultiplier (heatSymbol ν t) (𝓕 (complexifyL2 u)))) := rfl
example : ℝ≥0 → ℝ≥0 → SpatialL2 →L[ℝ] SpatialL2 := heatL2CLM
example (ν t : ℝ≥0) : heatL2CLM ν t = realFourierMultiplierCLM (heatSymbol ν t) := rfl
example (ν t : ℝ≥0) (u : SpatialL2) :
    heatL2CLM ν t u = heatL2 ν t u := heatL2CLM_apply ν t u
example (ν t : ℝ≥0) (u : SpatialL2) :
    (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
      (𝓕 (complexifyL2 (heatL2 ν t u)) : ComplexL2) ξ) =ᵐ[volume]
        (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
          (heatValue ν t ξ : ℂ) • (𝓕 (complexifyL2 u) : ComplexL2) ξ) :=
  heatL2_fourier_ae ν t u
example (ν t : ℝ≥0) (u : SpatialL2) :
    (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
      (𝓕 (complexifyL2 (heatL2 ν t u)) : ComplexL2) ξ) =ᵐ[volume]
        (fun ξ : MethbokeAddon.QuasiFeffermanA.Space =>
          (Real.exp (-(4 * Real.pi ^ 2 * (ν : ℝ) * (t : ℝ) * ‖ξ‖ ^ 2)) : ℂ) •
            (𝓕 (complexifyL2 u) : ComplexL2) ξ) :=
  heatL2_fourier_ae ν t u
example (ν t : ℝ≥0) (u v : SpatialL2) :
    heatL2 ν t (u + v) = heatL2 ν t u + heatL2 ν t v := heatL2_add ν t u v
example (ν t : ℝ≥0) (r : ℝ) (u : SpatialL2) :
    heatL2 ν t (r • u) = r • heatL2 ν t u := heatL2_smul ν t r u
example (ν t : ℝ≥0) : heatL2 ν t 0 = 0 := heatL2_zero ν t
example (ν t : ℝ≥0) (u : SpatialL2) : ‖heatL2 ν t u‖ ≤ ‖u‖ := norm_heatL2_le ν t u
example (ν : ℝ≥0) (u : SpatialL2) : heatL2 ν 0 u = u := heatL2_zero_time ν u
example (t : ℝ≥0) (u : SpatialL2) : heatL2 0 t u = u := heatL2_zero_viscosity t u
example (ν s t : ℝ≥0) (u : SpatialL2) :
    heatL2 ν (s + t) u = heatL2 ν s (heatL2 ν t u) := heatL2_add_time ν s t u
example (ν t s : ℝ≥0) (u : SpatialL2) :
    ‖heatL2 ν t u - heatL2 ν s u‖ ^ 2 =
      ∫ ξ : MethbokeAddon.QuasiFeffermanA.Space,
        (heatValue ν t ξ - heatValue ν s ξ) ^ 2 *
          ‖(𝓕 (complexifyL2 u) : ComplexL2) ξ‖ ^ 2 :=
  heatL2_sub_norm_sq_eq_fourier ν t s u
example (ν : ℝ≥0) (u : SpatialL2) : Continuous (fun t : ℝ≥0 => heatL2 ν t u) :=
  heatL2_continuous ν u

-- The physical lift proves the derivative relation for the actual multiplier output.
example (ν t : ℝ≥0) {v : SpatialL2} {G : Fin 3 → SpatialL2}
    (h : SpatialWeakGradient v G) :
    SpatialWeakGradient (heatL2 ν t v) (fun j => heatL2 ν t (G j)) :=
  spatialWeakGradient_heatL2 ν t h
example (ν t : ℝ≥0) {v : SpatialL2} {G : Fin 3 → SpatialL2}
    (h : SpatialWeakGradient v G) :
    ∀ j : Fin 3, ∀ ψ : MethbokeAddon.QuasiFeffermanA.Space → ℝ,
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) ψ → HasCompactSupport ψ →
        (∫ x : MethbokeAddon.QuasiFeffermanA.Space,
          fderiv ℝ ψ x (coordinateVector j) • heatL2 ν t v x) =
          -(∫ x : MethbokeAddon.QuasiFeffermanA.Space,
            ψ x • heatL2 ν t (G j) x) :=
  spatialWeakGradient_heatL2 ν t h
example : ℝ≥0 → ℝ≥0 → PhysicalH1 → PhysicalH1 := heatH1
example (ν t : ℝ≥0) (u : PhysicalH1) :
    heatH1 ν t u = physicalH1OfWeakGradient (heatL2 ν t (physicalH1Velocity u))
      (fun j => heatL2 ν t (physicalH1Gradient j u))
      (spatialWeakGradient_heatL2 ν t (physicalH1_weakGradient u)) := rfl
example (ν t : ℝ≥0) (u : PhysicalH1) :
    physicalH1Velocity (heatH1 ν t u) = heatL2 ν t (physicalH1Velocity u) :=
  heatH1_velocity ν t u
example (ν t : ℝ≥0) (u : PhysicalH1) (j : Fin 3) :
    physicalH1Gradient j (heatH1 ν t u) = heatL2 ν t (physicalH1Gradient j u) :=
  heatH1_gradient ν t u j
example (ν t : ℝ≥0) (u v : PhysicalH1) :
    heatH1 ν t (u + v) = heatH1 ν t u + heatH1 ν t v := heatH1_add ν t u v
example (ν t : ℝ≥0) (r : ℝ) (u : PhysicalH1) :
    heatH1 ν t (r • u) = r • heatH1 ν t u := heatH1_smul ν t r u
example (ν t : ℝ≥0) : heatH1 ν t 0 = 0 := heatH1_zero ν t
example (ν t : ℝ≥0) (u : PhysicalH1) :
    ‖heatH1 ν t u‖ ^ 2 ≤ ‖u‖ ^ 2 := heatH1_norm_sq_le ν t u
example (ν t : ℝ≥0) (u : PhysicalH1) : ‖heatH1 ν t u‖ ≤ ‖u‖ := norm_heatH1_le ν t u
example : ℝ≥0 → ℝ≥0 → PhysicalH1 →L[ℝ] PhysicalH1 := heatH1CLM
example (ν t : ℝ≥0) (u : PhysicalH1) :
    heatH1CLM ν t u = heatH1 ν t u := heatH1CLM_apply ν t u
example (ν : ℝ≥0) (u : PhysicalH1) : heatH1 ν 0 u = u := heatH1_zero_time ν u
example (t : ℝ≥0) (u : PhysicalH1) : heatH1 0 t u = u := heatH1_zero_viscosity t u
example (ν s t : ℝ≥0) (u : PhysicalH1) :
    heatH1 ν (s + t) u = heatH1 ν s (heatH1 ν t u) := heatH1_add_time ν s t u
example (ν t : ℝ≥0) (u : PhysicalH1) :
    physicalH1Energy (heatH1 ν t u) ≤ physicalH1Energy u := heatH1_energy_le ν t u
example (ν t : ℝ≥0) (u : PhysicalH1) :
    ‖physicalH1Velocity (heatH1 ν t u)‖ ^ 2 ≤ ‖physicalH1Velocity u‖ ^ 2 :=
  heatH1_energy_le ν t u
example (ν t : ℝ≥0) (u : PhysicalH1) :
    physicalH1Enstrophy (heatH1 ν t u) ≤ physicalH1Enstrophy u :=
  heatH1_enstrophy_le ν t u
example (ν t : ℝ≥0) (u : PhysicalH1) :
    (∑ j : Fin 3, ‖physicalH1Gradient j (heatH1 ν t u)‖ ^ 2) ≤
      ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2 := heatH1_enstrophy_le ν t u
example (ν : ℝ≥0) (u : PhysicalH1) : Continuous (fun t : ℝ≥0 => heatH1 ν t u) :=
  heatH1_continuous ν u

end QFAHeatSemigroup.ExpectedTypes

-- Ordered named type and axiom evidence.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_pos"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_pos
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_pos"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_le_one"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_le_one
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_le_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_le_one"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_le_one
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_le_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_frequency"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_frequency
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_frequency"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_frequency"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_frequency
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_frequency"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_continuous_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_neg"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_neg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_neg"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_viscosity"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_viscosity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_viscosity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_viscosity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_viscosity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_zero_viscosity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_add_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_add_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_add_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_add_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_add_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatValue_add_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol_value"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol_value
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol_value"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol_value"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol_value
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatSymbol_value"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2CLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_fourier_ae"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_fourier_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_fourier_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_fourier_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_fourier_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_fourier_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_smul"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatL2_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatL2_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatL2_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatL2_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatL2_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatL2_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_viscosity"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_viscosity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_viscosity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_viscosity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_viscosity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_zero_viscosity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_add_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_sub_norm_sq_eq_fourier"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_sub_norm_sq_eq_fourier
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_sub_norm_sq_eq_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_sub_norm_sq_eq_fourier"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_sub_norm_sq_eq_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_sub_norm_sq_eq_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_continuous"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatL2_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.spatialWeakGradient_heatL2"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.spatialWeakGradient_heatL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.spatialWeakGradient_heatL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.spatialWeakGradient_heatL2"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.spatialWeakGradient_heatL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.spatialWeakGradient_heatL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_velocity"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_gradient"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_smul"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_norm_sq_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_norm_sq_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatH1_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatH1_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatH1_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatH1_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatH1_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.norm_heatH1_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1CLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_viscosity"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_viscosity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_viscosity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_viscosity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_viscosity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_zero_viscosity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add_time"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_add_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_energy_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_energy_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_energy_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_energy_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_energy_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_energy_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_enstrophy_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_enstrophy_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_enstrophy_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_enstrophy_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_enstrophy_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_enstrophy_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_continuous"
#check @MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_continuous
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_continuous"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatSemigroup.heatH1_continuous"
