import MethbokeAddon.QuasiFeffermanA.Energy
import MethbokeAddon.QuasiFeffermanA.Cutoff

/-!
# Physical energy-class selection in the finite safe window

The actual whole-space weak equation and energy-class contract supply the
energy product and a full-measure set of solenoidal weak-gradient energy
starts. The scalar cutoff then selects one of those times. No global strong
reference or continuation theorem is a premise or conclusion of this layer.
The positive scalar `S` still needs a separate admissible Sobolev inequality.

Prepared for matching external compilation and exact type/axiom audits.
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Representation

/-- The actual trace properties obtained at almost every energy start.
This includes translated energy/trace data, not shifted weak-PDE membership. -/
def GoodRestart (ν : ℝ) (u : Velocity) (G : WeakGradient) (s : ℝ) : Prop :=
  Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
    EnergyStart ν u G s ∧ QFA.Assembly.Restart.RestartData ν u G s

theorem LerayHopf.goodRestart_ae
    {ν R : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (hR : 0 < R) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R), GoodRestart ν u G s := by
  exact h.ae_restart_energy_data hν hR

/-- At least half of the safe window consists of genuine energy-class good
traces with strict product smallness, and one such time lies strictly inside.
No Sobolev admissibility is inferred merely from `S > 0`. -/
theorem LerayHopf.safe_window_good_time_and_measure
    {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hS : 0 < S) (hν : 0 < ν) (ha : a ≠ 0) :
    (safeCutoff S ‖a‖ ν / 2 ≤
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S ‖a‖ ν))).real
        {s | GoodRestart ν u G s ∧
          velocityEnergy (u s) * gradientEnergy (G s) < productThreshold S ν}) ∧
      ∃ s, 0 < s ∧ s < safeCutoff S ‖a‖ ν ∧ GoodRestart ν u G s ∧
        velocityEnergy (u s) * gradientEnergy (G s) < productThreshold S ν := by
  have hM : ‖a‖ ≠ 0 := ne_of_gt (norm_pos_iff.mpr ha)
  have hR : 0 < safeCutoff S ‖a‖ ν := safeCutoff_pos hS hν hM
  obtain ⟨hprod, hbudget⟩ := h.energy_product_budget_Ioo hν hR
  have hgood := h.goodRestart_ae hν.le hR
  have hprodnn : ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) (safeCutoff S ‖a‖ ν)),
      0 ≤ velocityEnergy (u s) * gradientEnergy (G s) := by
    filter_upwards with s
    exact mul_nonneg (velocityEnergy_nonneg (u s)) (gradientEnergy_nonneg (G s))
  exact ⟨good_set_measure_ge_half_of_product_budget hS hν hprod hprodnn hgood hbudget,
    exists_good_time_of_product_budget hS hν hM hprod hgood hbudget⟩

/-- Expanded selected-time endpoint: actual weak-gradient trace, admissible
energy start, strong right trace and strict product bound before the cutoff. -/
theorem LerayHopf.exists_safe_restart
    {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hS : 0 < S) (hν : 0 < ν) (ha : a ≠ 0) :
    ∃ s, 0 < s ∧ s < safeCutoff S ‖a‖ ν ∧
      Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
      EnergyStart ν u G s ∧ QFA.Assembly.Restart.RestartData ν u G s ∧
      Tendsto u (𝓝[>] s) (𝓝 (u s)) ∧
      velocityEnergy (u s) * gradientEnergy (G s) < productThreshold S ν := by
  obtain ⟨s, hs0, hsR, hgood, hsmall⟩ :=
    (h.safe_window_good_time_and_measure hS hν ha).2
  rcases hgood with ⟨hsol, hgrad, hstart, hdata⟩
  exact ⟨s, hs0, hsR, hsol, hgrad, hstart, hdata,
    h.strong_right_trace hν.le hs0.le hstart, hsmall⟩

end MethbokeAddon.QuasiFeffermanA
