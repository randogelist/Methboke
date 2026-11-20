import MethbokeAddon.FeffermanFamily.LocalBlowup
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Choose

/-!
# Selecting a growth sequence from global preterminal speed unboundedness

The hypothesis below is the terminal-time generalization of the literal
`SpeedUnboundedAtOne` predicate in the pinned source
`openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd`,
`NavierStokes/ProblemStatement.lean`. It does not assert that a field satisfies
that hypothesis, import the upstream seed, or change the project toolchain.

At integer index `n`, choice uses speed threshold `n + 1` and remaining-time
radius `1 / (n + 1)`. The resulting quantitative bounds imply both time
convergence and norm divergence. A common compact spatial carrier then gives
an actual local blowup point through the already accepted compactness helper.

This is the sequence-selection part of F02. Seed existence, recentering and
same-force NSE comparison remain separate obligations. No local Lean execution.
-/

open Filter Set
open scoped Topology

namespace MethbokeAddon.FeffermanFamily

universe u v

variable {X : Type u} {E : Type v}
variable [PseudoMetricSpace X] [NormedAddCommGroup E]

/-- Arbitrarily large speed at some spatial point in every positive-time
left neighborhood of `T`. This does not yet specify a spatial blowup point. -/
def SpeedUnboundedAt (U : ℝ → X → E) (T : ℝ) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : X,
      t ∈ Ioo (0 : ℝ) T ∧ T - δ < t ∧ M < ‖U t x‖

/-- Local velocity blowup implies the spatially unlocalized speed predicate. -/
theorem LocalVelocityBlowup.speedUnboundedAt
    {U : ℝ → X → E} {a : X} {T : ℝ}
    (hU : LocalVelocityBlowup U a T) : SpeedUnboundedAt U T := by
  intro M hM δ hδ
  obtain ⟨t, x, ht, htT, hgap, _, hlarge⟩ := hU M hM 1 zero_lt_one δ hδ
  exact ⟨t, x, ⟨ht, htT⟩, by linarith, hlarge⟩

namespace SpeedUnboundedAt

variable {U : ℝ → X → E} {T : ℝ}

/-- The predicate itself forces a positive terminal time. -/
theorem terminal_pos (hU : SpeedUnboundedAt U T) : 0 < T := by
  obtain ⟨t, x, ht, _, _⟩ := hU 1 zero_lt_one 1 zero_lt_one
  exact ht.1.trans ht.2

/-- Select a sequence with explicit time-error and speed-growth bounds.
The two limiting conclusions are derived, not additional input hypotheses. -/
theorem exists_growth_sequence (hU : SpeedUnboundedAt U T) :
    ∃ t : ℕ → ℝ, ∃ x : ℕ → X,
      (∀ n : ℕ, 0 < t n ∧ t n < T) ∧
      (∀ n : ℕ, T - t n < 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ‖U (t n) (x n)‖) ∧
      Tendsto t atTop (𝓝 T) ∧
      Tendsto (fun n => ‖U (t n) (x n)‖) atTop atTop := by
  have hchoice : ∀ n : ℕ, ∃ t : ℝ, ∃ x : X,
      (0 < t ∧ t < T) ∧ T - t < 1 / ((n : ℝ) + 1) ∧
        (n : ℝ) + 1 < ‖U t x‖ := by
    intro n
    have hn : 0 < (n : ℝ) + 1 := by linarith [(show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
    obtain ⟨t, x, ht, hgap, hlarge⟩ :=
      hU ((n : ℝ) + 1) hn (1 / ((n : ℝ) + 1)) (one_div_pos.mpr hn)
    exact ⟨t, x, ht, by linarith, hlarge⟩
  choose t x ht hgap hlarge using hchoice
  have htend : Tendsto t atTop (𝓝 T) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hrecip : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have hnear : ∀ᶠ n : ℕ in atTop, dist (1 / ((n : ℝ) + 1)) 0 < ε :=
      Metric.tendsto_nhds.mp hrecip ε hε
    exact hnear.mono fun n hn => by
      have hsmall : 1 / ((n : ℝ) + 1) < ε := by
        have habs : |1 / ((n : ℝ) + 1)| < ε := by
          simpa only [Real.dist_eq, sub_zero] using hn
        exact (le_abs_self _).trans_lt habs
      rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (ht n).2)]
      linarith [hgap n]
  have hnorm : Tendsto (fun n => ‖U (t n) (x n)‖) atTop atTop := by
    apply tendsto_atTop.2
    intro M
    have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have hge : ∀ᶠ n : ℕ in atTop, M ≤ (n : ℝ) :=
      hnat.eventually (eventually_ge_atTop M)
    exact hge.mono fun n hn => by linarith [hlarge n]
  exact ⟨t, x, ht, hgap, hlarge, htend, hnorm⟩

/-- If every positive preterminal slice vanishes outside `K`, the selected
large-speed points lie in `K`; no spatial compactness is needed for this step. -/
theorem exists_growth_sequence_in_carrier (hU : SpeedUnboundedAt U T)
    (K : Set X)
    (hzero : ∀ t, 0 < t → t < T → ∀ x, x ∉ K → U t x = 0) :
    ∃ t : ℕ → ℝ, ∃ x : ℕ → X,
      (∀ n : ℕ, 0 < t n ∧ t n < T) ∧
      (∀ n : ℕ, x n ∈ K) ∧
      (∀ n : ℕ, T - t n < 1 / ((n : ℝ) + 1)) ∧
      (∀ n : ℕ, (n : ℝ) + 1 < ‖U (t n) (x n)‖) ∧
      Tendsto t atTop (𝓝 T) ∧
      Tendsto (fun n => ‖U (t n) (x n)‖) atTop atTop := by
  obtain ⟨t, x, ht, hgap, hlarge, htend, hnorm⟩ := hU.exists_growth_sequence
  have hxK : ∀ n : ℕ, x n ∈ K := by
    intro n
    by_contra hx
    have hz : U (t n) (x n) = 0 := hzero (t n) (ht n).1 (ht n).2 (x n) hx
    have hn : (n : ℝ) + 1 < 0 := by simpa only [hz, norm_zero] using hlarge n
    linarith [(show 0 ≤ (n : ℝ) from Nat.cast_nonneg n)]
  exact ⟨t, x, ht, hxK, hgap, hlarge, htend, hnorm⟩

/-- Global speed unboundedness plus one compact spatial carrier yields a
local blowup point. The speed predicate remains an explicit hypothesis. -/
theorem exists_localVelocityBlowup (hU : SpeedUnboundedAt U T)
    (K : Set X) (hK : IsCompact K)
    (hzero : ∀ t, 0 < t → t < T → ∀ x, x ∉ K → U t x = 0) :
    ∃ a ∈ K, LocalVelocityBlowup U a T := by
  obtain ⟨t, x, ht, hxK, _, _, htend, hnorm⟩ :=
    hU.exists_growth_sequence_in_carrier K hzero
  exact exists_localVelocityBlowup_of_compact_sequence U K hK T t x ht htend hxK hnorm

end SpeedUnboundedAt

end MethbokeAddon.FeffermanFamily
