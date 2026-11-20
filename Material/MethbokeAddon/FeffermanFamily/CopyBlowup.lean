import MethbokeAddon.FeffermanFamily.LocalBlowup
import Mathlib.Analysis.Normed.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Transport of local blowup to delayed compressed copies

These metric and algebraic lemmas transport an already supplied local blowup
property. They neither construct a singular seed nor assert preservation of the
Navier--Stokes equation. In particular, the time-compression lemma only uses
strictly positive preterminal source times. Its pullback times stay strictly
between zero and one when the clock coefficient is at least one.

The final formula is the velocity scaling used for a delayed parabolic copy,
with terminal time one and a freely chosen spatial center. PDE, support,
energy, force-admission and periodization adapters are separate obligations.
-/

namespace MethbokeAddon.FeffermanFamily
namespace LocalVelocityBlowup

universe u v

section Translation

variable {X : Type u} {E : Type v}
variable [NormedAddCommGroup X] [NormedAddCommGroup E]
variable {U : ℝ → X → E} {b : X} {T : ℝ}

/-- Translation transports the point of local blowup by the same vector. -/
theorem spatial_translate (hU : LocalVelocityBlowup U b T) (a : X) :
    LocalVelocityBlowup (fun t x => U t (x - a)) (b + a) T := by
  intro M hM ε hε δ hδ
  obtain ⟨t, x, ht, htT, htime, hspace, hlarge⟩ := hU M hM ε hε δ hδ
  refine ⟨t, x + a, ht, htT, htime, ?_, ?_⟩
  · simpa only [dist_add_right] using hspace
  · simpa only [add_sub_cancel_right] using hlarge

/-- A local blowup point can be moved to the origin by recentering. -/
theorem recenter (hU : LocalVelocityBlowup U b T) :
    LocalVelocityBlowup (fun t x => U t (x + b)) 0 T := by
  simpa only [sub_neg_eq_add, add_neg_cancel] using hU.spatial_translate (-b)

end Translation

section Amplitude

variable {X : Type u} {E : Type v}
variable [PseudoMetricSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : ℝ → X → E} {a : X} {T : ℝ}

/-- A strictly positive constant velocity amplitude preserves local blowup. -/
theorem positive_smul (hU : LocalVelocityBlowup U a T)
    (c : ℝ) (hc : 0 < c) :
    LocalVelocityBlowup (fun t x => c • U t x) a T := by
  intro M hM ε hε δ hδ
  obtain ⟨t, x, ht, htT, htime, hspace, hlarge⟩ :=
    hU (M / c) (div_pos hM hc) ε hε δ hδ
  refine ⟨t, x, ht, htT, htime, hspace, ?_⟩
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hc]
  have hmul := (div_lt_iff₀ hc).mp hlarge
  simpa only [mul_comm] using hmul

end Amplitude

section SpaceScaling

variable {X : Type u} {E : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup E]
variable {U : ℝ → X → E} {T : ℝ}

/-- A positive spatial dilation preserves local blowup at the origin. -/
theorem positive_spatial_scale (hU : LocalVelocityBlowup U 0 T)
    (c : ℝ) (hc : 0 < c) :
    LocalVelocityBlowup (fun t x => U t (c • x)) 0 T := by
  intro M hM ε hε δ hδ
  obtain ⟨t, x, ht, htT, htime, hspace, hlarge⟩ :=
    hU M hM (c * ε) (mul_pos hc hε) δ hδ
  refine ⟨t, c⁻¹ • x, ht, htT, htime, ?_, ?_⟩
  · rw [dist_zero_right, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hc)]
    have hnorm : ‖x‖ < ε * c := by
      simpa only [dist_zero_right, mul_comm] using hspace
    have hdiv : ‖x‖ / c < ε := (div_lt_iff₀ hc).mpr hnorm
    simpa only [div_eq_mul_inv, mul_comm] using hdiv
  · simpa only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] using hlarge

end SpaceScaling

section TimeScaling

variable {X : Type u} {E : Type v}
variable [PseudoMetricSpace X] [NormedAddCommGroup E]
variable {U : ℝ → X → E} {a : X}

/-- An affine clock fixing time one preserves local blowup. The clock
coefficient at least one ensures positive pullback times for every positive
preterminal source time. -/
theorem time_compress_at_one (hU : LocalVelocityBlowup U a 1)
    (c : ℝ) (hc : 1 ≤ c) :
    LocalVelocityBlowup (fun t x => U (1 + c * (t - 1)) x) a 1 := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  intro M hM ε hε δ hδ
  obtain ⟨s, x, hs, hs1, htime, hspace, hlarge⟩ :=
    hU M hM ε hε (c * δ) (mul_pos hcpos hδ)
  have hremain : 0 < (1 - s) / c := div_pos (by linarith) hcpos
  have hremain_lt_one : (1 - s) / c < 1 := by
    apply (div_lt_iff₀ hcpos).mpr
    linarith
  have hremain_lt_delta : (1 - s) / c < δ := by
    apply (div_lt_iff₀ hcpos).mpr
    simpa only [mul_comm] using htime
  have hclock : 1 + c * ((1 - (1 - s) / c) - 1) = s := by
    field_simp [hcpos.ne']
    <;> ring
  refine ⟨1 - (1 - s) / c, x, ?_, ?_, ?_, hspace, ?_⟩
  · linarith
  · linarith
  · linarith
  · simpa only [hclock] using hlarge

end TimeScaling

section ParabolicCopy

variable {X : Type u} {E : Type v}
variable [NormedAddCommGroup X] [NormedSpace ℝ X]
variable [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {U : ℝ → X → E}

/-- The velocity of a delayed compressed copy has local blowup at its chosen
center. This is geometric transport only, not a PDE-preservation theorem. -/
theorem parabolic_copy (hU : LocalVelocityBlowup U 0 1)
    (scale : ℝ) (hscale : 1 < scale) (a : X) :
    LocalVelocityBlowup
      (fun t x => scale • U (1 + scale ^ 2 * (t - 1)) (scale • (x - a))) a 1 := by
  have hscalepos : 0 < scale := lt_trans zero_lt_one hscale
  have hscalesq : 1 ≤ scale ^ 2 := by nlinarith [sq_nonneg (scale - 1)]
  have htime := hU.time_compress_at_one (scale ^ 2) hscalesq
  have hspace := htime.positive_spatial_scale scale hscalepos
  have hamp := hspace.positive_smul scale hscalepos
  simpa only [zero_add] using hamp.spatial_translate a

end ParabolicCopy

end LocalVelocityBlowup
end MethbokeAddon.FeffermanFamily
