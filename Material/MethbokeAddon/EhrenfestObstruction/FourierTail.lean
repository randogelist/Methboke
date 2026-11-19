import MethbokeAddon.EhrenfestObstruction.SmoothReference

/-!
The actual H2-to-H1 reference tail, with the canonical positive cutoff N=n+1.
The quantitative tail estimate is reused from SingularClosure.TorusSobolev.
Prepared source only; external cached compilation and audits remain pending.
-/

set_option autoImplicit false

open Set SingularClosure
open MethbokeAddon.WeakFouriermanB

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

/-- The actual high-frequency reference remainder, as an H1 coefficient state. -/
def referenceH1Tail (n : ℕ) (c : TorusSobolev 2) : TorusSobolev 1 :=
  torusSobolevInclusion 1 c -
    torusSobolevCutoff 1 (n + 1) (torusSobolevInclusion 1 c)

/-- One extra Sobolev derivative gives the exact positive-cutoff tail rate. -/
theorem referenceH1Tail_norm_le (n : ℕ) (c : TorusSobolev 2) :
    ‖referenceH1Tail n c‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * ‖c‖ :=
  torusSobolevInclusion_tail 1 (n + 1) (Nat.succ_pos n) c

/-- Mean-zero states identify the Sobolev cutoff with the literal Galerkin cutoff. -/
theorem referenceH1Tail_coeff (n : ℕ) (c : TorusSobolev 2)
    (hc : ∀ i : Fin 3, c.val 0 i = 0) :
    (referenceH1Tail n c).val = c.val - cutoffCoeff (n + 1) c.val := by
  have hzero : ∀ i : Fin 3, (torusSobolevInclusion 1 c).val 0 i = 0 := by
    simpa only [torusSobolevInclusion_coeff] using hc
  change (torusSobolevInclusion 1 c).val -
    (torusSobolevCutoff 1 (n + 1) (torusSobolevInclusion 1 c)).val = _
  rw [torusSobolevCutoff_eq_galerkinCutoff 1 (n + 1)
    (torusSobolevInclusion 1 c) hzero, torusSobolevInclusion_coeff]

/-- A uniform H2 bound gives a uniform n-indexed H1 tail bound. -/
theorem referenceH1Tail_norm_le_of_norm_le
    (n : ℕ) (c : TorusSobolev 2) (K : ℝ) (hK : ‖c‖ ≤ K) :
    ‖referenceH1Tail n c‖ ≤ ((n + 1 : ℕ) : ℝ)⁻¹ * K := by
  exact (referenceH1Tail_norm_le n c).trans
    (mul_le_mul_of_nonneg_left hK (inv_nonneg.mpr (Nat.cast_nonneg _)))

/-- The reference tail is the literal unprojected-minus-Galerkin coefficient array. -/
theorem initial_front_H1_tail_coeff
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (n : ℕ) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) :
    (referenceH1Tail n (initialFrontSobolev 2 ν S a u p H t ht)).val =
      datumFourierCoeff (u t) - cutoffCoeff (n + 1) (datumFourierCoeff (u t)) := by
  exact referenceH1Tail_coeff n _
    (initialFrontSobolev_meanZero 2 ν S a u p H t ht)

/-- Uniform reference tails are derived from the actual initial classical front. -/
theorem initial_front_uniform_H1_tail
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (T : ℝ) (hTS : T < S) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ n t (ht : t ∈ Icc (0 : ℝ) T),
      ‖referenceH1Tail n
        (initialFrontSobolev 2 ν S a u p H t ⟨ht.1, ht.2.trans_lt hTS⟩)‖ ≤
        ((n + 1 : ℕ) : ℝ)⁻¹ * K := by
  obtain ⟨K, hK, hbound⟩ := initial_front_uniform_sobolev_norm ν S a u p H 2 T hTS
  refine ⟨K, hK, ?_⟩
  intro n t ht
  exact referenceH1Tail_norm_le_of_norm_le n _ K (hbound t ht)

end
end MethbokeAddon.EhrenfestObstruction
