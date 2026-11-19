import QuasiFeffermanB.SpatialAdmission
import QuasiFeffermanB.Endpoints.LerayHopfExistence
import SingularClosure.CriticalSmoothCancellation
import SingularClosure.CriticalRelativeEnergyIntegrable

/-! Smooth physical datum admission to the original QFB energy class.

This independent WFB-08 input adapter does not construct a local strong
solution, a maximal trajectory, or a continuation theorem. It preserves the
actual datum almost everywhere and identifies the literal QFB cutoff.

Prepared source only; external compiler/type/axiom verification is pending.
-/

set_option autoImplicit false
set_option Elab.async true

open Set MeasureTheory SingularClosure QuasiFeffermanB
open scoped ContDiff ENNReal Topology

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

theorem smooth_datum_memLp {a : Field} (ha : SmoothSigmaZero a) :
    MemLp a 2 (volume.restrict unitCube) :=
  critical_continuous_memLp_cube a ha.smooth.continuous 2

theorem smooth_datum_representative_ae {a : Field} (ha : SmoothSigmaZero a) :
    (criticalL2Representative a : Field) =ᵐ[volume.restrict unitCube] a := by
  rw [criticalL2Representative_eq a (smooth_datum_memLp ha)]
  exact (smooth_datum_memLp ha).coeFn_toLp

theorem smooth_datum_constant_pairing_zero {a : Field}
    (ha : SmoothSigmaZero a) (i : Fin 3) :
    physicalFieldInner a (fun _ => unitVector i) = 0 := by
  rw [physical_constant_pairing_coordinate]
  have hi : (∫ x in unitCube, a x i) = spatialMean a i :=
    (EuclideanSpace.proj i : Vec →L[ℝ] ℝ).integral_comp_comm ha.mean_zero.1
  rw [hi, ha.mean_zero.2]
  rfl

theorem smooth_datum_energySigmaZero {a : Field} (ha : SmoothSigmaZero a) :
    EnergySigmaZero (criticalL2Representative a) := by
  constructor
  · intro p hp hpp
    rw [physical_inner_congr_left_ae (smooth_datum_representative_ae ha)]
    exact critical_smooth_integral_inner_gradient_eq_zero a p ha.smooth hp
      ha.periodic hpp ha.divergence_free
  · intro i
    rw [physical_inner_congr_left_ae (smooth_datum_representative_ae ha)]
    exact smooth_datum_constant_pairing_zero ha i

theorem smooth_datum_representative_norm_sq {a : Field}
    (ha : SmoothSigmaZero a) :
    ‖criticalL2Representative a‖ ^ 2 = physicalEnergy a :=
  criticalL2Representative_norm_sq a (smooth_datum_memLp ha)

theorem smooth_datum_cutoff {a : Field} (ha : SmoothSigmaZero a) (ν : ℝ) :
    cutoff (criticalL2Representative a) ν =
      (physicalEnergy a) ^ 2 / (8 * Real.pi ^ 2 * ν ^ 5) := by
  unfold cutoff
  have hpow : ‖criticalL2Representative a‖ ^ 4 = (physicalEnergy a) ^ 2 := by
    rw [← smooth_datum_representative_norm_sq ha]
    ring
  rw [hpow]

/-- Q01 supplies an original Leray--Hopf solution for the actual smooth datum.
The initial representative equality is explicit; no local strong solution is
assumed or concluded. -/
theorem smooth_datum_lerayHopf_exists
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a) :
    ∃ (u : Velocity) (G : WeakGradientTrajectory),
      CriticalLerayHopf ν (criticalL2Representative a) u G ∧
      u 0 =ᵐ[volume.restrict unitCube] a := by
  obtain ⟨u, G, hu⟩ := Q01_LERAY_HOPF_EXISTENCE ν hν
    (criticalL2Representative a) (smooth_datum_energySigmaZero ha)
  exact ⟨u, G, hu, hu.initial.trans (smooth_datum_representative_ae ha)⟩

end

end MethbokeAddon.WeakFouriermanB
