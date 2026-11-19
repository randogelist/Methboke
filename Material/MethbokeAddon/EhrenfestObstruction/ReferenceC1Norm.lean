import MethbokeAddon.EhrenfestObstruction.SmoothReference
import SingularClosure.PeriodicSobolev

/-!
# Actual velocity and Frechet operator norm bounds for the reference front

Finite-dimensional component estimates give uniform projected norms. Compactness
of the actual spatial derivative fields gives the original reference derivative
bound, including time zero. No norm-bound certificate is assumed.

Prepared source only; external cached compilation and axiom audits are required.
No local Lean/Lake/kernel execution was used.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

/-- A common absolute component bound controls the actual Euclidean norm. -/
theorem vec_norm_le_two_mul_of_component_abs_le
    (v : Vec) (B : ℝ) (hB : 0 ≤ B) (h : ∀ i : Fin 3, |v i| ≤ B) :
    ‖v‖ ≤ 2 * B := by
  have hcomponent (i : Fin 3) : (v i) ^ 2 ≤ B ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v i)) hB).mpr (h i)
  have hsquare : ‖v‖ ^ 2 ≤ 3 * B ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq]
    calc
      _ ≤ ∑ _i : Fin 3, B ^ 2 := Finset.sum_le_sum (fun i _ => hcomponent i)
      _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]
  apply (sq_le_sq₀ (norm_nonneg v) (mul_nonneg (by norm_num) hB)).mp
  nlinarith [sq_nonneg B]

/-- The native coordinate decomposition controls the actual Frechet operator norm. -/
theorem fderiv_norm_le_sum_coordinate_norm (v : Field) (x : Vec) :
    ‖fderiv ℝ v x‖ ≤ ∑ j : Fin 3, ‖coordinateDerivative v j x‖ := by
  simpa only [coordinateDerivative] using
    opNorm_le_sum_coordinate_norm (fderiv ℝ v x)

/-- A common bound on the three coordinate derivative vectors controls fderiv. -/
theorem fderiv_norm_le_three_mul_of_coordinate_norm_le
    (v : Field) (x : Vec) (B : ℝ)
    (h : ∀ j : Fin 3, ‖coordinateDerivative v j x‖ ≤ B) :
    ‖fderiv ℝ v x‖ ≤ 3 * B := by
  calc
    _ ≤ ∑ j : Fin 3, ‖coordinateDerivative v j x‖ :=
      fderiv_norm_le_sum_coordinate_norm v x
    _ ≤ ∑ _j : Fin 3, B := Finset.sum_le_sum (fun j _ => h j)
    _ = _ := by simp [Finset.sum_const, nsmul_eq_mul]

/-- A common bound on all nine derivative components gives an operator bound. -/
theorem fderiv_norm_le_six_mul_of_component_abs_le
    (v : Field) (x : Vec) (B : ℝ) (hB : 0 ≤ B)
    (h : ∀ j i : Fin 3, |coordinateDerivative v j x i| ≤ B) :
    ‖fderiv ℝ v x‖ ≤ 6 * B := by
  calc
    _ ≤ 3 * (2 * B) := fderiv_norm_le_three_mul_of_coordinate_norm_le v x (2 * B)
      (fun j => vec_norm_le_two_mul_of_component_abs_le
        (coordinateDerivative v j x) B hB (h j))
    _ = _ := by ring

/-- Joint initial-front smoothness gives a uniform actual spatial derivative norm. -/
theorem initial_joint_smooth_uniform_fderiv_norm
    (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (initialFrontSpacetime S))
    (T : ℝ) (hTS : T < S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t (ht : t ∈ Icc (0 : ℝ) T) (x : Vec)
      (hx : x ∈ unitCube), ‖fderiv ℝ (u t) x‖ ≤ C := by
  have hsum : ContinuousOn
      (fun z : ℝ × Vec => ∑ j : Fin 3, ‖coordinateDerivative (u z.1) j z.2‖)
      (initialFrontSpacetime S) := by
    apply continuousOn_finset_sum
    intro j _
    exact (initial_coordinateDerivative_contDiffOn u S hu j).continuousOn.norm
  have hsubset : Icc (0 : ℝ) T ×ˢ unitCube ⊆ initialFrontSpacetime S := by
    intro z hz
    exact ⟨hz.1.1, hz.1.2.trans_lt hTS⟩
  obtain ⟨C, hC⟩ :=
    ((isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).prod isCompact_unitCube).exists_bound_of_continuousOn
      (hsum.mono hsubset)
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro t ht x hx
  have hCt : |∑ j : Fin 3, ‖coordinateDerivative (u t) j x‖| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC (t, x) ⟨ht, hx⟩
  exact (fderiv_norm_le_sum_coordinate_norm (u t) x).trans
    ((le_abs_self _).trans (hCt.trans (le_max_right _ _)))

/-- One actual uniform norm bound for the projected velocity, its derivative,
and the original reference derivative on every shorter closed physical slab. -/
theorem initial_front_uniform_C1_norms
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (T : ℝ) (hTS : T < S) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ N t (ht : t ∈ Icc (0 : ℝ) T) (x : Vec)
      (hx : x ∈ unitCube),
      ‖finiteSynthesis N (datumFourierCoeff (u t)) x‖ ≤ M ∧
      ‖fderiv ℝ (finiteSynthesis N (datumFourierCoeff (u t))) x‖ ≤ M ∧
      ‖fderiv ℝ (u t) x‖ ≤ M := by
  obtain ⟨B, hB, hprojected⟩ :=
    initial_front_uniform_projected_C1_components ν S a u p H T hTS
  obtain ⟨C, hC, hreference⟩ :=
    initial_joint_smooth_uniform_fderiv_norm u S H.velocity_smooth T hTS
  have hB0 : 0 ≤ B := le_trans zero_le_one hB
  refine ⟨max (6 * B) C, hC.trans (le_max_right _ _), ?_⟩
  intro N t ht x hx
  have h := hprojected N t ht x
  refine ⟨?_, ?_, (hreference t ht x hx).trans (le_max_right _ _)⟩
  · exact (vec_norm_le_two_mul_of_component_abs_le
      (finiteSynthesis N (datumFourierCoeff (u t)) x) B hB0 h.1).trans
      ((mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ) ≤ 6) hB0).trans
        (le_max_left _ _))
  · exact (fderiv_norm_le_six_mul_of_component_abs_le
      (finiteSynthesis N (datumFourierCoeff (u t))) x B hB0 h.2).trans
      (le_max_left _ _)

end
end MethbokeAddon.EhrenfestObstruction
