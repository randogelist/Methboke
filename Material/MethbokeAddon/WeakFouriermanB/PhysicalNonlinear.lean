import MethbokeAddon.WeakFouriermanB.HomogeneousBudget
import SingularClosure.PeriodicFourierInjective
import SingularClosure.EnstrophyAbsorption

/-!
The actual arbitrary-field Hessian identity and nonlinear enstrophy estimate.
Fourier injectivity is used only to commute literal spatial operators. All
norms and pairings in the estimates are physical cube integrals. No Fourier
support, Galerkin trajectory, solution existence, or assumed inequality is
required. Prepared source; external cached verification is required.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff ENNReal NNReal RealInnerProductSpace

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

def physicalLaplacianSquare (v : Field) : ℝ :=
  ∫ x in unitCube, ‖laplacian v x‖ ^ 2

theorem physicalLaplacianSquare_nonneg (v : Field) :
    0 ≤ physicalLaplacianSquare v :=
  integral_nonneg (fun _ => sq_nonneg _)

theorem physical_dissipation_nonneg (v : Field) :
    0 ≤ physicalDissipation v := by
  unfold physicalDissipation
  apply integral_nonneg
  intro x
  rw [gradientSquareDensity_eq_sum_norm_sq]
  exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)

/-- Commutation for literal operators on arbitrary smooth periodic fields. -/
theorem physical_laplacian_coordinateDerivative_commute
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3) :
    laplacian (coordinateDerivative v i) = coordinateDerivative (laplacian v) i := by
  apply datumFourierCoeff_injective_continuous_periodic
  · exact (laplacian_contDiff _ (coordinateDerivative_smooth hv i)).continuous
  · exact (coordinateDerivative_smooth (laplacian_contDiff v hv) i).continuous
  · exact laplacian_spatialPeriodic _ (coordinateDerivative_spatialPeriodic i v hp)
  · exact coordinateDerivative_spatialPeriodic i _ (laplacian_spatialPeriodic v hp)
  · rw [datumFourierCoeff_laplacian _ (coordinateDerivative_smooth hv i)
        (coordinateDerivative_spatialPeriodic i v hp),
      datumFourierCoeff_coordinateDerivative i v hv hp,
      datumFourierCoeff_coordinateDerivative i _ (laplacian_contDiff v hv)
        (laplacian_spatialPeriodic v hp),
      datumFourierCoeff_laplacian v hv hp]
    funext k j
    simp only [laplacianCoefficient, spectralMultiplier]
    ring

/-- Every periodic spatial derivative has actual zero mean. -/
theorem physical_coordinateDerivative_meanZero
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3) :
    MeanZero (coordinateDerivative v i) := by
  have hi : IntegrableOn (coordinateDerivative v i) unitCube volume :=
    (coordinateDerivative_continuous hv i).continuousOn.integrableOn_compact isCompact_unitCube
  refine ⟨hi, ?_⟩
  ext j
  change spatialMean (coordinateDerivative v i) j = 0
  have hz : datumFourierCoeff (coordinateDerivative v i) 0 j = 0 := by
    rw [datumFourierCoeff_coordinateDerivative i v hv hp]
    simp [spectralMultiplier, derivativeSymbol]
  rw [datumFourierCoeff_zero hi] at hz
  exact_mod_cast hz

/-- No finite-synthesis premise: the physical Hessian square equals the
physical Laplacian square for every smooth periodic vector field. -/
theorem physical_hessian_laplacian_eq
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    (∑ i : Fin 3, physicalDissipation (coordinateDerivative v i)) =
      physicalLaplacianSquare v := by
  have hterm (i : Fin 3) :
      physicalDissipation (coordinateDerivative v i) =
        ∫ x in unitCube,
          inner ℝ (coordinateDerivative (coordinateDerivative v i) i x) (laplacian v x) := by
    have h := critical_integral_inner_coordinateDerivative
      (coordinateDerivative v i) (laplacian v) (coordinateDerivative_smooth hv i)
      (laplacian_contDiff v hv) (coordinateDerivative_spatialPeriodic i v hp)
      (laplacian_spatialPeriodic v hp) i
    rw [← physical_laplacian_coordinateDerivative_commute v hv hp i,
      critical_integral_inner_laplacian_self _ (coordinateDerivative_smooth hv i)
        (coordinateDerivative_spatialPeriodic i v hp)] at h
    linarith
  simp_rw [hterm]
  rw [← integral_finsetSum Finset.univ (fun i _ =>
    ((coordinateDerivative_smooth (coordinateDerivative_smooth hv i) i).continuous.inner
      (laplacian_contDiff v hv).continuous).continuousOn.integrableOn_compact
        isCompact_unitCube)]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [← sum_inner]
  change inner ℝ (laplacian v x) (laplacian v x) = ‖laplacian v x‖ ^ 2
  exact real_inner_self_eq_norm_sq _

theorem physical_coordinateDissipation_le_laplacianSquare
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3) :
    physicalDissipation (coordinateDerivative v i) ≤ physicalLaplacianSquare v := by
  rw [← physical_hessian_laplacian_eq v hv hp]
  exact Finset.single_le_sum (fun j _ => physical_dissipation_nonneg _) (Finset.mem_univ i)

theorem physical_fderiv_eLpNorm_two_le
    (v : Field) (hv : ContDiff ℝ ∞ v) :
    eLpNorm (fderiv ℝ v) 2 (volume.restrict unitCube) ≤
      (3 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (physicalDissipation v)) ^ (1 / 2 : ℝ) := by
  have hd : Continuous (fderiv ℝ v) := (hv.fderiv_right (m := 0) (by norm_num)).continuous
  have hi : IntegrableOn (fun x => ‖fderiv ℝ v x‖ ^ 2) unitCube volume :=
    (hd.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  have hI : (∫ x in unitCube, ‖fderiv ℝ v x‖ ^ 2) ≤ 3 * physicalDissipation v := by
    calc
      _ ≤ ∫ x in unitCube, 3 * gradientSquareDensity v x :=
        integral_mono hi ((gradientSquareDensity_integrableOn hv).const_mul 3)
          (fun x => fderiv_norm_sq_le_three_gradientSquareDensity v x)
      _ = _ := by rw [integral_const_mul]; rfl
  rw [eLpNorm_two_eq_integral_norm_sq_rpow _ _ hi]
  calc
    _ ≤ (ENNReal.ofReal (3 * physicalDissipation v)) ^ (1 / 2 : ℝ) :=
      ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hI) (by norm_num)
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num), ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
      norm_num

theorem physical_eLpNorm_two_le_dissipation
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (hz : MeanZero v) :
    eLpNorm v 2 (volume.restrict unitCube) ≤
      (ENNReal.ofReal (physicalDissipation v)) ^ (1 / 2 : ℝ) := by
  have hi : IntegrableOn (fun x => ‖v x‖ ^ 2) unitCube volume :=
    (hv.continuous.norm.pow 2).continuousOn.integrableOn_compact isCompact_unitCube
  rw [eLpNorm_two_eq_integral_norm_sq_rpow _ _ hi, ← physicalEnergy_eq_integral_norm_sq]
  exact ENNReal.rpow_le_rpow
    (ENNReal.ofReal_le_ofReal (smooth_periodic_meanZero_energy_le_dissipation v hv hp hz))
    (by norm_num)

theorem physical_laplacian_eLpNorm_two
    (v : Field) (hv : ContDiff ℝ ∞ v) :
    eLpNorm (laplacian v) 2 (volume.restrict unitCube) =
      (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (1 / 2 : ℝ) := by
  exact eLpNorm_two_eq_integral_norm_sq_rpow _ _
    (((laplacian_contDiff v hv).continuous.norm.pow 2).continuousOn.integrableOn_compact
      isCompact_unitCube)

/-- The constant is fixed before the arbitrary physical field. -/
theorem PHYSICAL_L6_FROM_DISSIPATION :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v : Field, ContDiff ℝ ∞ v → SpatialPeriodic v →
      MeanZero v → eLpNorm v 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (physicalDissipation v)) ^ (1 / 2 : ℝ) := by
  obtain ⟨K, hK0, hK⟩ := PERIODIC_SOBOLEV_H1_L6 (F := Vec)
  let C : ℝ≥0∞ :=
    (SNormLESNormFDerivOfEqConst Vec (volume : Measure Vec) 2 : ℝ≥0∞) *
      (343 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) + ENNReal.ofReal K)
  refine ⟨C, by dsimp [C]; finiteness, ?_⟩
  intro v hv hp hz
  have hD := physical_fderiv_eLpNorm_two_le v hv
  have hV := physical_eLpNorm_two_le_dissipation v hv hp hz
  calc
    _ ≤ _ := hK v hv hp
    _ ≤ (SNormLESNormFDerivOfEqConst Vec (volume : Measure Vec) 2 : ℝ≥0∞) *
        (343 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
        ((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
          (ENNReal.ofReal (physicalDissipation v)) ^ (1 / 2 : ℝ) +
          ENNReal.ofReal K * (ENNReal.ofReal (physicalDissipation v)) ^ (1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (add_le_add hD (mul_le_mul_of_nonneg_left hV bot_le)) bot_le
    _ = _ := by dsimp [C]; ring

theorem PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v : Field, ContDiff ℝ ∞ v → SpatialPeriodic v →
      eLpNorm (fderiv ℝ v) 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (1 / 2 : ℝ) := by
  obtain ⟨C, hC, hSob⟩ := PHYSICAL_L6_FROM_DISSIPATION
  refine ⟨3 * C, by finiteness, ?_⟩
  intro v hv hp
  have hcoord (i : Fin 3) :
      eLpNorm (coordinateDerivative v i) 6 (volume.restrict unitCube) ≤
        C * (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (1 / 2 : ℝ) :=
    (hSob _ (coordinateDerivative_smooth hv i) (coordinateDerivative_spatialPeriodic i v hp)
      (physical_coordinateDerivative_meanZero v hv hp i)).trans
        (mul_le_mul_of_nonneg_left (ENNReal.rpow_le_rpow
          (ENNReal.ofReal_le_ofReal (physical_coordinateDissipation_le_laplacianSquare v hv hp i))
          (by norm_num)) bot_le)
  have hmeas (i : Fin 3) : AEStronglyMeasurable
      (fun x => ‖coordinateDerivative v i x‖) (volume.restrict unitCube) :=
    (coordinateDerivative_continuous hv i).norm.aestronglyMeasurable
  calc
    _ ≤ eLpNorm (fun x => ∑ i : Fin 3, ‖coordinateDerivative v i x‖) 6
        (volume.restrict unitCube) :=
      eLpNorm_mono_real (fun x => opNorm_le_sum_coordinate_norm (fderiv ℝ v x))
    _ ≤ ∑ i : Fin 3, eLpNorm (fun x => ‖coordinateDerivative v i x‖) 6
        (volume.restrict unitCube) := by
      have hsum : (fun x => ∑ i : Fin 3, ‖coordinateDerivative v i x‖) =
          ∑ i : Fin 3, (fun x => ‖coordinateDerivative v i x‖) := by
        funext x
        simp only [Finset.sum_apply]
      rw [hsum]
      exact eLpNorm_sum_le (s := Finset.univ) (fun i _ => hmeas i)
        (by norm_num : (1 : ℝ≥0∞) ≤ 6)
    _ = ∑ i : Fin 3, eLpNorm (coordinateDerivative v i) 6
        (volume.restrict unitCube) := by simp only [eLpNorm_norm]
    _ ≤ ∑ _i : Fin 3, C * (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (1 / 2 : ℝ) :=
      Finset.sum_le_sum (fun i _ => hcoord i)
    _ = _ := by simp; ring

theorem PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND :
    ∃ C : ℝ≥0∞, C < ⊤ ∧ ∀ v : Field, ContDiff ℝ ∞ v → SpatialPeriodic v →
      MeanZero v → ENNReal.ofReal (abs (∫ x in unitCube,
        inner ℝ (convection v x) (laplacian v x))) ≤
          C * (ENNReal.ofReal (physicalDissipation v)) ^ (3 / 4 : ℝ) *
            (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (3 / 4 : ℝ) := by
  obtain ⟨A, hA, hSob⟩ := PHYSICAL_L6_FROM_DISSIPATION
  obtain ⟨B, hB, hDeriv⟩ := PHYSICAL_DERIVATIVE_L6_FROM_LAPLACIAN
  refine ⟨A * (3 : ℝ≥0∞) ^ (1 / 4 : ℝ) * B ^ (1 / 2 : ℝ), by finiteness, ?_⟩
  intro v hv hp hz
  have hd : Continuous (fderiv ℝ v) := (hv.fderiv_right (m := 0) (by norm_num)).continuous
  have hconv : Continuous (convection v) := hd.clm_apply hv.continuous
  have hlap := (laplacian_contDiff v hv).continuous
  have hD3 := cube_eLpNorm_three_le_interpolation (fderiv ℝ v) hd
  have hD2 := physical_fderiv_eLpNorm_two_le v hv
  have hD6 := hDeriv v hv hp
  have hV6 := hSob v hv hp hz
  calc
    _ ≤ eLpNorm (convection v) 2 (volume.restrict unitCube) *
        eLpNorm (laplacian v) 2 (volume.restrict unitCube) :=
      inner_integral_enorm_le_eLpNorm_two _ _ hconv hlap
    _ ≤ (eLpNorm v 6 (volume.restrict unitCube) *
        eLpNorm (fderiv ℝ v) 3 (volume.restrict unitCube)) *
        (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (1 / 2 : ℝ) := by
      rw [physical_laplacian_eLpNorm_two v hv]
      exact mul_le_mul_of_nonneg_right (convection_eLpNorm_two_le v hv) bot_le
    _ ≤ ((A * (ENNReal.ofReal (physicalDissipation v)) ^ (1 / 2 : ℝ)) *
        (((3 : ℝ≥0∞) ^ (1 / 2 : ℝ) *
            (ENNReal.ofReal (physicalDissipation v)) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ) *
          (B * (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (1 / 2 : ℝ)) ^ (1 / 2 : ℝ))) *
        (ENNReal.ofReal (physicalLaplacianSquare v)) ^ (1 / 2 : ℝ) := by
      apply mul_le_mul_of_nonneg_right _ bot_le
      refine mul_le_mul hV6 ?_ bot_le bot_le
      exact hD3.trans (mul_le_mul
        (ENNReal.rpow_le_rpow hD2 (by norm_num))
        (ENNReal.rpow_le_rpow hD6 (by norm_num)) bot_le bot_le)
    _ = _ := ennreal_three_quarter_product _ _ _ _

theorem PHYSICAL_NONLINEAR_REAL_BOUND :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ v : Field, ContDiff ℝ ∞ v → SpatialPeriodic v →
      MeanZero v → abs (∫ x in unitCube,
        inner ℝ (convection v x) (laplacian v x)) ≤
          K * (physicalDissipation v) ^ (3 / 4 : ℝ) *
            (physicalLaplacianSquare v) ^ (3 / 4 : ℝ) := by
  obtain ⟨C, hC, hbound⟩ := PHYSICAL_NONLINEAR_THREE_QUARTER_BOUND
  refine ⟨C.toReal, ENNReal.toReal_nonneg, ?_⟩
  intro v hv hp hz
  have h := ENNReal.toReal_mono (by finiteness) (hbound v hv hp hz)
  simpa only [ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (abs_nonneg _),
    ENNReal.toReal_ofReal (physical_dissipation_nonneg v),
    ENNReal.toReal_ofReal (physicalLaplacianSquare_nonneg v)] using h

/-- The nonlinear absorption has a universal constant and no evolution premise. -/
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

end
end MethbokeAddon.WeakFouriermanB
