import MethbokeAddon.EhrenfestObstruction.FourierTail
import MethbokeAddon.EhrenfestObstruction.ProjectedC1
import MethbokeAddon.WeakFouriermanB.PhysicalFourier
import SingularClosure.CriticalGalerkin
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# The actual physical reference tail

The physical L2 energy and physical gradient energy of the literal remainder
U - P_N U are bounded by its actual H1 coefficient norm. The harmless factor
12 comes from separate bounds on three velocity and nine gradient components.
No physical remainder-bound premise is introduced.

Prepared source only; matching external cached compilation and audits required.
No local Lean/Lake/kernel execution was used.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

/-- An actual H0 state bounds the full square sum of any one component. -/
theorem torusSobolev_H0_component_tsum_norm_sq_le
    (c : TorusSobolev 0) (i : Fin 3) :
    (∑' k : Frequency, ‖c.val k i‖ ^ 2) ≤ ‖c‖ ^ 2 := by
  apply tsum_le_of_sum_le' (sq_nonneg ‖c‖)
  intro s
  have h := torusSobolev_finite_weighted_sum_le 0 c
    (s.product ({i} : Finset (Fin 3)))
  have hproduct :
      (∑ ki ∈ s.product ({i} : Finset (Fin 3)),
        ‖sobolevWeightedCoeff 0 c.val ki‖ ^ 2) =
      ∑ k ∈ s, ∑ j ∈ ({i} : Finset (Fin 3)),
        ‖sobolevWeightedCoeff 0 c.val (k, j)‖ ^ 2 :=
    Finset.sum_product s ({i} : Finset (Fin 3))
      (fun ki : FourierIndex => ‖sobolevWeightedCoeff 0 c.val ki‖ ^ 2)
  rw [hproduct] at h
  simpa only [Finset.sum_singleton, torusSobolev_weightedCoeff_norm,
    pow_zero, one_mul] using h

/-- Smooth physical scalar Parseval, stated for the original physical field. -/
theorem smooth_periodic_component_parseval
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3) :
    (∫ x in unitCube, (v x i) ^ 2) =
      ∑' k : Frequency, ‖datumFourierCoeff v k i‖ ^ 2 := by
  have hr := ALL_SOBOLEV_IMP_RAPID_SCALAR (datumFourierCoeff v)
    (fun s => SMOOTH_DATUM_MEM_TORUS_SOBOLEV s v hv hp)
  have h := critical_smoothFourierSynthesis_component_parseval
    (datumFourierCoeff v) hr (datumFourierCoeff_reality v) i
  simpa only [smoothFourierSynthesis_datum_eq v hv hp,
    Complex.normSq_eq_norm_sq] using h

/-- The actual physical energy is controlled by the actual H0 coefficient state. -/
theorem smooth_periodic_physicalEnergy_le_H0_norm_sq
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 0) (hc : c.val = datumFourierCoeff v) :
    physicalEnergy v ≤ 3 * ‖c‖ ^ 2 := by
  have hcomponent (i : Fin 3) : (∫ x in unitCube, (v x i) ^ 2) ≤ ‖c‖ ^ 2 := by
    rw [smooth_periodic_component_parseval v hv hp i, ← hc]
    exact torusSobolev_H0_component_tsum_norm_sq_le c i
  unfold physicalEnergy
  rw [integral_finsetSum Finset.univ
    (f := fun i x => (v x i) ^ 2) (μ := volume.restrict unitCube)
    (fun i _ => (((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp
      hv.continuous).pow 2).continuousOn.integrableOn_compact isCompact_unitCube)]
  calc
    _ ≤ ∑ _i : Fin 3, ‖c‖ ^ 2 := Finset.sum_le_sum (fun i _ => hcomponent i)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]

/-- One-order inclusion controls the actual physical velocity energy. -/
theorem smooth_periodic_physicalEnergy_le_H1_norm_sq
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 1) (hc : c.val = datumFourierCoeff v) :
    physicalEnergy v ≤ 3 * ‖c‖ ^ 2 := by
  have hcoeff : (torusSobolevInclusionLinear 0 c).val = datumFourierCoeff v := by
    rw [torusSobolevInclusionLinear_coeff, hc]
  have h := smooth_periodic_physicalEnergy_le_H0_norm_sq v hv hp
    (torusSobolevInclusionLinear 0 c) hcoeff
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _) (torusSobolevInclusion_norm_le 0 c) 2)
    (by norm_num))

/-- The actual derivative multiplier controls the physical gradient energy. -/
theorem smooth_periodic_physicalDissipation_le_H1_norm_sq
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 1) (hc : c.val = datumFourierCoeff v) :
    physicalDissipation v ≤ 9 * ‖c‖ ^ 2 := by
  have hcoordinate (j : Fin 3) :
      physicalEnergy (coordinateDerivative v j) ≤ 3 * ‖c‖ ^ 2 := by
    have hd : ContDiff ℝ ∞ (coordinateDerivative v j) :=
      (contDiff_infty_iff_fderiv.mp hv).2.clm_apply contDiff_const
    have hdp : SpatialPeriodic (coordinateDerivative v j) :=
      coordinateDerivative_spatialPeriodic j v hp
    have hcoeff : (ehrenfestTorusSobolevCoordinateDerivative 0 j c).val =
        datumFourierCoeff (coordinateDerivative v j) := by
      rw [ehrenfestTorusSobolevCoordinateDerivative_coeff, hc,
        datumFourierCoeff_coordinateDerivative j v hv hp]
    have h := smooth_periodic_physicalEnergy_le_H0_norm_sq
      (coordinateDerivative v j) hd hdp
      (ehrenfestTorusSobolevCoordinateDerivative 0 j c) hcoeff
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _)
        (ehrenfestTorusSobolevCoordinateDerivative_norm_le 0 j c) 2)
      (by norm_num))
  rw [physicalDissipation, integral_gradientSquareDensity_eq_sum_physicalEnergy v hv]
  calc
    _ ≤ ∑ _j : Fin 3, 3 * ‖c‖ ^ 2 :=
      Finset.sum_le_sum (fun j _ => hcoordinate j)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]; ring

/-- A physical H1 bound proved from coefficient identification and scalar Parseval. -/
theorem smooth_periodic_physical_H1_le_torusSobolev
    (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 1) (hc : c.val = datumFourierCoeff v) :
    (∫ x in unitCube, ‖v x‖ ^ 2) + physicalDissipation v ≤ 12 * ‖c‖ ^ 2 := by
  have hE := smooth_periodic_physicalEnergy_le_H1_norm_sq v hv hp c hc
  have hD := smooth_periodic_physicalDissipation_le_H1_norm_sq v hv hp c hc
  rw [physicalEnergy_eq_integral_norm_sq] at hE
  linarith

/-- Actual physical Fourier integration commutes with field subtraction. -/
theorem ehrenfest_datumFourierCoeff_sub (a b : Field)
    (ha : Continuous a) (hb : Continuous b) :
    datumFourierCoeff (a - b) = datumFourierCoeff a - datumFourierCoeff b := by
  funext k i
  unfold datumFourierCoeff datumFourierIntegrand
  simp only [Pi.sub_apply, PiLp.sub_apply, Complex.ofReal_sub, mul_sub]
  exact integral_sub (datumFourierIntegrand_integrableOn ha k i)
    (datumFourierIntegrand_integrableOn hb k i)

/-- Literal physical remainder after the original nonzero Fourier cutoff. -/
def physicalReferenceTail (N : ℕ) (v : Field) : Field :=
  v - finiteSynthesis N (datumFourierCoeff v)

theorem physicalReferenceTail_smooth (N : ℕ) (v : Field)
    (hv : ContDiff ℝ ∞ v) : ContDiff ℝ ∞ (physicalReferenceTail N v) :=
  hv.sub (finiteSynthesis_contDiff N (datumFourierCoeff v))

theorem physicalReferenceTail_periodic (N : ℕ) (v : Field)
    (hp : SpatialPeriodic v) : SpatialPeriodic (physicalReferenceTail N v) := by
  intro x j
  change v (x + unitVector j) -
      finiteSynthesis N (datumFourierCoeff v) (x + unitVector j) =
    v x - finiteSynthesis N (datumFourierCoeff v) x
  rw [hp x j, finiteSynthesis_periodic N (datumFourierCoeff v) x j]

theorem physicalReferenceTail_coeff (N : ℕ) (v : Field) (hv : Continuous v) :
    datumFourierCoeff (physicalReferenceTail N v) =
      datumFourierCoeff v - cutoffCoeff N (datumFourierCoeff v) := by
  rw [physicalReferenceTail, ehrenfest_datumFourierCoeff_sub v
    (finiteSynthesis N (datumFourierCoeff v)) hv
      (finiteSynthesis_contDiff N (datumFourierCoeff v)).continuous,
    criticalGalerkin_datumFourierCoeff_finiteSynthesis N (datumFourierCoeff v)
      (datumFourierCoeff_reality v)]

/-- The actual physical remainder is bounded by the concrete H1 tail state. -/
theorem physicalReferenceTail_physical_H1_le
    (n : ℕ) (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 2) (hc : c.val = datumFourierCoeff v)
    (hz : ∀ i : Fin 3, c.val 0 i = 0) :
    (∫ x in unitCube, ‖physicalReferenceTail (n + 1) v x‖ ^ 2) +
      physicalDissipation (physicalReferenceTail (n + 1) v) ≤
        12 * ‖referenceH1Tail n c‖ ^ 2 := by
  apply smooth_periodic_physical_H1_le_torusSobolev
    (physicalReferenceTail (n + 1) v)
    (physicalReferenceTail_smooth (n + 1) v hv)
    (physicalReferenceTail_periodic (n + 1) v hp) (referenceH1Tail n c)
  rw [referenceH1Tail_coeff n c hz, hc,
    physicalReferenceTail_coeff (n + 1) v hv.continuous]

/-- Physical L2-plus-gradient decay at the actual positive Fourier cutoff. -/
theorem physicalReferenceTail_physical_H1_le_rate
    (n : ℕ) (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (c : TorusSobolev 2) (hc : c.val = datumFourierCoeff v)
    (hz : ∀ i : Fin 3, c.val 0 i = 0) :
    (∫ x in unitCube, ‖physicalReferenceTail (n + 1) v x‖ ^ 2) +
      physicalDissipation (physicalReferenceTail (n + 1) v) ≤
        12 * (((n + 1 : ℕ) : ℝ)⁻¹ * ‖c‖) ^ 2 := by
  exact (physicalReferenceTail_physical_H1_le n v hv hp c hc hz).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (referenceH1Tail_norm_le n c) 2)
      (by norm_num))

/-- The coefficient state in the physical estimate can be constructed directly from v. -/
theorem smoothDatum_physicalReferenceTail_physical_H1_le_rate
    (n : ℕ) (v : Field) (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    (hz : SpectralMeanZero (datumFourierCoeff v)) :
    (∫ x in unitCube, ‖physicalReferenceTail (n + 1) v x‖ ^ 2) +
      physicalDissipation (physicalReferenceTail (n + 1) v) ≤
        12 * (((n + 1 : ℕ) : ℝ)⁻¹ * ‖smoothDatumSobolev 2 v hv hp‖) ^ 2 :=
  physicalReferenceTail_physical_H1_le_rate n v hv hp
    (smoothDatumSobolev 2 v hv hp) (smoothDatumSobolev_coeff 2 v hv hp) hz

/-- Uniform physical reference-tail decay on every strictly shorter closed slab. -/
theorem initial_front_uniform_physical_H1_tail
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (T : ℝ) (hTS : T < S) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n t (ht : t ∈ Icc (0 : ℝ) T),
      (∫ x in unitCube, ‖physicalReferenceTail (n + 1) (u t) x‖ ^ 2) +
        physicalDissipation (physicalReferenceTail (n + 1) (u t)) ≤
          12 * (((n + 1 : ℕ) : ℝ)⁻¹ * K) ^ 2 := by
  obtain ⟨K, hK, hbound⟩ := initial_front_uniform_sobolev_norm ν S a u p H 2 T hTS
  refine ⟨K, hK, ?_⟩
  intro n t ht
  have htime : t ∈ Ico (0 : ℝ) S := ⟨ht.1, ht.2.trans_lt hTS⟩
  have hs := initial_front_smooth_slices ν S a u p H t htime
  have h := physicalReferenceTail_physical_H1_le n (u t) hs.smooth hs.periodic
    (initialFrontSobolev 2 ν S a u p H t htime)
    (initialFrontSobolev_coeff 2 ν S a u p H t htime)
    (initialFrontSobolev_meanZero 2 ν S a u p H t htime)
  exact h.trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (norm_nonneg _)
      (referenceH1Tail_norm_le_of_norm_le n
        (initialFrontSobolev 2 ν S a u p H t htime) K (hbound t ht)) 2)
    (by norm_num))

end
end MethbokeAddon.EhrenfestObstruction
