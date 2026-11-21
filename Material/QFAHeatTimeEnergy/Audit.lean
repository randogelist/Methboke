import QFAHeatTimeEnergy.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform NNReal Topology

namespace QFAHeatTimeEnergy.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSemigroup
open MethbokeAddon.QuasiFeffermanA.HeatSmoothing
open MethbokeAddon.QuasiFeffermanA.HeatTrajectory
open MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy
open QFA.Endpoints.Agmon (ComplexL2)
open QFA.Endpoints.Representation

-- Literal physical Fourier normalization and density, independent of its abbreviation.
example (u : PhysicalH1) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    enstrophyDensity u ξ = (2 * Real.pi) ^ 2 * ‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2 := rfl
example (u : PhysicalH1) (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    0 ≤ enstrophyDensity u ξ := enstrophyDensity_nonneg u ξ
example (u : PhysicalH1) : Integrable (enstrophyDensity u) volume :=
  integrable_enstrophyDensity u
example (u : PhysicalH1) :
    (∫ ξ : MethbokeAddon.QuasiFeffermanA.Space, enstrophyDensity u ξ) =
      ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2 := integral_enstrophyDensity u
example (ν t : ℝ≥0) (u : PhysicalH1) :
    physicalH1Enstrophy (heatH1 ν t u) =
      ∫ ξ : MethbokeAddon.QuasiFeffermanA.Space,
        Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * (t : ℝ)) * enstrophyDensity u ξ :=
  heatH1_enstrophy_eq_integral ν t u
example (ν : ℝ≥0) (u : PhysicalH1) (t : ℝ)
    (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    heatDissipationDensity ν u t ξ =
      heatRate ξ * Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * t) * enstrophyDensity u ξ := rfl
example (ν : ℝ≥0) (u : PhysicalH1) (t : ℝ)
    (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    0 ≤ heatDissipationDensity ν u t ξ := heatDissipationDensity_nonneg ν u t ξ
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T)
    (ξ : MethbokeAddon.QuasiFeffermanA.Space) :
    (∫ t in Ioc (0 : ℝ) T, heatDissipationDensity ν u t ξ) =
      (2 * (ν : ℝ))⁻¹ * (enstrophyDensity u ξ -
        Real.exp (-(2 * (ν : ℝ) * heatRate ξ) * T) * enstrophyDensity u ξ) :=
  integral_heatDissipationDensity_time ν hν u T hT ξ
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    Integrable (fun q : MethbokeAddon.QuasiFeffermanA.Space × ℝ =>
      heatDissipationDensity ν u q.2 q.1)
      ((volume : Measure MethbokeAddon.QuasiFeffermanA.Space).prod
        (volume.restrict (Ioc (0 : ℝ) T))) :=
  integrable_heatDissipationDensity_prod ν hν u T hT
example (ν t : ℝ≥0) (hν : 0 < ν) (ht : 0 < t) (u : PhysicalH1) :
    ‖physicalH2Laplacian (heatH1ToH2 ν t hν ht u)‖ ^ 2 =
      ∫ ξ : MethbokeAddon.QuasiFeffermanA.Space, heatDissipationDensity ν u (t : ℝ) ξ :=
  heatH1ToH2_laplacian_norm_sq_eq_integral ν t hν ht u
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) {t : ℝ} (ht : 0 < t) :
    ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2 =
      ∫ ξ : MethbokeAddon.QuasiFeffermanA.Space, heatDissipationDensity ν u t ξ :=
  heatTrajectory_laplacian_norm_sq_eq_integral ν hν u ht
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun t : ℝ => ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2)
      (Ioc (0 : ℝ) T) volume := heatTrajectory_laplacian_sq_integrableOn ν hν u T hT
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    IntervalIntegrable (fun t : ℝ => ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2)
      volume 0 T := heatTrajectory_laplacian_sq_intervalIntegrable ν hν u T hT
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2) =
      (2 * (ν : ℝ))⁻¹ *
        (physicalH1Enstrophy u - physicalH1Enstrophy (heatH1 ν T.toNNReal u)) :=
  heatTrajectory_laplacian_sq_integral ν hν u T hT
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    2 * (ν : ℝ) *
      (∫ t in (0 : ℝ)..T, ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2) =
        (∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2) -
        (∑ j : Fin 3, ‖physicalH1Gradient j (heatH1 ν T.toNNReal u)‖ ^ 2) :=
  heatTrajectory_enstrophy_dissipation ν hν u T hT
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖physicalH2Laplacian (heatTrajectory ν hν u t)‖ ^ 2) ≤
      physicalH1Enstrophy u / (2 * (ν : ℝ)) :=
  heatTrajectory_laplacian_sq_integral_le ν hν u T hT
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    IntegrableOn (fun t : ℝ => ‖heatTrajectory ν hν u t‖ ^ 2)
      (Ioc (0 : ℝ) T) volume := heatTrajectory_norm_sq_integrableOn ν hν u T hT
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    MemLp (heatTrajectory ν hν u) 2 (volume.restrict (Ioc (0 : ℝ) T)) :=
  heatTrajectory_memLp_two ν hν u T hT
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, ‖heatTrajectory ν hν u t‖ ^ 2) ≤
      T * ‖u‖ ^ 2 + (∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2) / (2 * (ν : ℝ)) :=
  heatTrajectory_norm_sq_integral_le ν hν u T hT

-- Ordinary positive real viscosity has the identical factor, with no restricted
-- input class, H2 initial-value assumption, or time-integrability premise.
example (ν : ℝ) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    2 * ν *
      (∫ t in (0 : ℝ)..T,
        ‖physicalH2Laplacian (heatTrajectory ν.toNNReal (Real.toNNReal_pos.mpr hν) u t)‖ ^ 2) =
        physicalH1Enstrophy u - physicalH1Enstrophy (heatH1 ν.toNNReal T.toNNReal u) := by
  simpa only [Real.coe_toNNReal ν hν.le] using
    heatTrajectory_enstrophy_dissipation ν.toNNReal (Real.toNNReal_pos.mpr hν) u T hT

-- Independently assembled physical endpoint with one actual trajectory.
example (ν : ℝ≥0) (hν : 0 < ν) (u : PhysicalH1) (T : ℝ) (hT : 0 ≤ T) :
    ∃ w : ℝ → PhysicalH2,
      StronglyMeasurable w ∧
      (∀ t : ℝ, 0 < t → physicalH2Velocity (w t) =
        heatL2 ν t.toNNReal (physicalH1Velocity u)) ∧
      MemLp w 2 (volume.restrict (Ioc (0 : ℝ) T)) ∧
      2 * (ν : ℝ) * (∫ t in (0 : ℝ)..T, ‖physicalH2Laplacian (w t)‖ ^ 2) =
        (∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2) -
          (∑ j : Fin 3, ‖physicalH1Gradient j (heatH1 ν T.toNNReal u)‖ ^ 2) :=
  ⟨heatTrajectory ν hν u, heatTrajectory_stronglyMeasurable ν hν u,
    fun t ht => heatTrajectory_velocity ν hν u ht,
    heatTrajectory_memLp_two ν hν u T hT,
    heatTrajectory_enstrophy_dissipation ν hν u T hT⟩

end QFAHeatTimeEnergy.ExpectedTypes

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity_nonneg"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity_nonneg"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.enstrophyDensity_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_enstrophyDensity"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_enstrophyDensity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_enstrophyDensity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_enstrophyDensity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_enstrophyDensity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_enstrophyDensity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_enstrophyDensity"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_enstrophyDensity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_enstrophyDensity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_enstrophyDensity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_enstrophyDensity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_enstrophyDensity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1_enstrophy_eq_integral"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1_enstrophy_eq_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1_enstrophy_eq_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1_enstrophy_eq_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1_enstrophy_eq_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1_enstrophy_eq_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity_nonneg"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity_nonneg"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatDissipationDensity_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_heatDissipationDensity_time"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_heatDissipationDensity_time
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_heatDissipationDensity_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_heatDissipationDensity_time"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_heatDissipationDensity_time
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integral_heatDissipationDensity_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_heatDissipationDensity_prod"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_heatDissipationDensity_prod
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_heatDissipationDensity_prod"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_heatDissipationDensity_prod"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_heatDissipationDensity_prod
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.integrable_heatDissipationDensity_prod"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1ToH2_laplacian_norm_sq_eq_integral"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1ToH2_laplacian_norm_sq_eq_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1ToH2_laplacian_norm_sq_eq_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1ToH2_laplacian_norm_sq_eq_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1ToH2_laplacian_norm_sq_eq_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatH1ToH2_laplacian_norm_sq_eq_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_norm_sq_eq_integral"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_norm_sq_eq_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_norm_sq_eq_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_norm_sq_eq_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_norm_sq_eq_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_norm_sq_eq_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integrableOn"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integrableOn
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integrableOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integrableOn"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integrableOn
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integrableOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_intervalIntegrable"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_intervalIntegrable
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_intervalIntegrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_intervalIntegrable"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_intervalIntegrable
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_intervalIntegrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_enstrophy_dissipation"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_enstrophy_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_enstrophy_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_enstrophy_dissipation"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_enstrophy_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_enstrophy_dissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral_le"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_laplacian_sq_integral_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integrableOn"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integrableOn
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integrableOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integrableOn"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integrableOn
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integrableOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_memLp_two"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_memLp_two
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_memLp_two"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_memLp_two"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_memLp_two
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_memLp_two"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integral_le"
#check MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integral_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integral_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integral_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integral_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatTimeEnergy.heatTrajectory_norm_sq_integral_le"
