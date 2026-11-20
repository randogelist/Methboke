import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Linarith

/-!
# Local velocity blowup and continuation obstructions

This module contains the metric/topological part of the prescribed-site family
route. It asserts no Navier--Stokes witness and imports no literature seed.
The time interval is genuinely left-open at the terminal time. In particular,
assigning an arbitrary value to a total function at that time cannot remove the
obstruction to a continuous extension.

The compact-carrier theorem below takes an explicit growth sequence. Selecting
such a sequence from the literature's global speed predicate, and importing
that seed at Methboke's dependency pin, remain separate adapters.
-/

open Filter Set
open scoped Topology

namespace MethbokeAddon.FeffermanFamily

universe u v

variable {X : Type u} {E : Type v}
variable [PseudoMetricSpace X] [NormedAddCommGroup E]

/-- Velocity becomes arbitrarily large in every left spacetime neighborhood
of `(T,a)`, using only strictly positive preterminal times. -/
def LocalVelocityBlowup (U : ℝ → X → E) (a : X) (T : ℝ) : Prop :=
  ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
    ∃ t : ℝ, ∃ x : X,
      0 < t ∧ t < T ∧ T - t < δ ∧ dist x a < ε ∧ M < ‖U t x‖

namespace LocalVelocityBlowup

variable {U V : ℝ → X → E} {a : X} {T : ℝ}

/-- Positive preterminal times force the terminal time to be positive. -/
theorem terminal_pos (hU : LocalVelocityBlowup U a T) : 0 < T := by
  obtain ⟨t, x, ht, htT, _⟩ := hU 1 zero_lt_one 1 zero_lt_one 1 zero_lt_one
  exact ht.trans htT

/-- Changing the values at or after the terminal time does not change the
preterminal blowup property. -/
theorem congr_on_left (hU : LocalVelocityBlowup U a T)
    (hagree : ∀ t, 0 < t → t < T → ∀ x, V t x = U t x) :
    LocalVelocityBlowup V a T := by
  intro M hM ε hε δ hδ
  obtain ⟨t, x, ht, htT, hδt, hεx, hlarge⟩ := hU M hM ε hε δ hδ
  refine ⟨t, x, ht, htT, hδt, hεx, ?_⟩
  simpa only [hagree t ht htT x] using hlarge

/-- A local blowup point has no finite bound on any left spacetime cylinder. -/
theorem not_locally_bounded (hU : LocalVelocityBlowup U a T) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ t x, 0 < t → t < T → T - t < δ → dist x a < ε → ‖U t x‖ ≤ C := by
  rintro ⟨ε, hε, δ, hδ, C, hbound⟩
  have hM : 0 < max C 1 := lt_of_lt_of_le zero_lt_one (le_max_right C 1)
  obtain ⟨t, x, ht, htT, hδt, hεx, hlarge⟩ := hU (max C 1) hM ε hε δ hδ
  exact (not_lt_of_ge ((hbound t x ht htT hδt hεx).trans (le_max_left C 1))) hlarge

/-- Local blowup is incompatible with joint continuity at the terminal point. -/
theorem not_continuousAt (hU : LocalVelocityBlowup U a T) :
    ¬ ContinuousAt (fun z : ℝ × X => U z.1 z.2) (T, a) := by
  intro hcont
  obtain ⟨r, hr, hsmall⟩ := Metric.continuousAt_iff.mp hcont 1 zero_lt_one
  have hM : 0 < ‖U T a‖ + 1 := by linarith [norm_nonneg (U T a)]
  obtain ⟨t, x, ht, htT, hrt, hrx, hlarge⟩ := hU (‖U T a‖ + 1) hM r hr r hr
  have htime : dist t T < r := by
    rw [Real.dist_eq, abs_of_neg (sub_neg.mpr htT)]
    linarith
  have hpair : dist (t, x) (T, a) < r := by
    simpa only [Prod.dist_eq, max_lt_iff] using And.intro htime hrx
  have hdiff : ‖U t x - U T a‖ < 1 := by
    simpa only [dist_eq_norm] using hsmall hpair
  have hnorm : ‖U t x‖ ≤ ‖U t x - U T a‖ + ‖U T a‖ :=
    norm_le_norm_sub_add (U t x) (U T a)
  linarith

/-- Any competing field that agrees at all positive preterminal times fails
to be jointly continuous at the blowup point. Same-force NSE uniqueness is a
separate obligation used to establish `hagree` in the family application. -/
theorem not_continuousAt_of_agrees (hU : LocalVelocityBlowup U a T)
    (V : ℝ → X → E)
    (hagree : ∀ t, 0 < t → t < T → ∀ x, V t x = U t x) :
    ¬ ContinuousAt (fun z : ℝ × X => V z.1 z.2) (T, a) :=
  (hU.congr_on_left hagree).not_continuousAt

/-- A preterminal sequence approaching the point with norms tending to
infinity supplies the quantitative local blowup predicate. -/
theorem of_sequence (t : ℕ → ℝ) (x : ℕ → X)
    (ht : ∀ n, 0 < t n ∧ t n < T)
    (htend : Tendsto t atTop (𝓝 T))
    (hxend : Tendsto x atTop (𝓝 a))
    (hlarge : Tendsto (fun n => ‖U (t n) (x n)‖) atTop atTop) :
    LocalVelocityBlowup U a T := by
  intro M hM ε hε δ hδ
  have htnear : ∀ᶠ n in atTop, dist (t n) T < δ :=
    Metric.tendsto_nhds.mp htend δ hδ
  have hxnear : ∀ᶠ n in atTop, dist (x n) a < ε :=
    Metric.tendsto_nhds.mp hxend ε hε
  have hnorm : ∀ᶠ n in atTop, M < ‖U (t n) (x n)‖ :=
    hlarge.eventually (eventually_gt_atTop M)
  obtain ⟨n, htn, hxn, hnormn⟩ := (htnear.and (hxnear.and hnorm)).exists
  refine ⟨t n, x n, (ht n).1, (ht n).2, ?_, hxn, hnormn⟩
  rw [Real.dist_eq, abs_of_neg (sub_neg.mpr (ht n).2)] at htn
  linarith

end LocalVelocityBlowup

/-- A compact carrier converts a spatially unlocalized growth sequence into
an actual local blowup point in that carrier. This is the compactness step of
F02; the literature seed and selection of the input sequence are not assumed
to have been formalized here. -/
theorem exists_localVelocityBlowup_of_compact_sequence
    (U : ℝ → X → E) (K : Set X) (hK : IsCompact K) (T : ℝ)
    (t : ℕ → ℝ) (x : ℕ → X)
    (ht : ∀ n, 0 < t n ∧ t n < T)
    (htend : Tendsto t atTop (𝓝 T))
    (hxK : ∀ n, x n ∈ K)
    (hlarge : Tendsto (fun n => ‖U (t n) (x n)‖) atTop atTop) :
    ∃ a ∈ K, LocalVelocityBlowup U a T := by
  obtain ⟨a, haK, φ, hφ, hxend⟩ := hK.tendsto_subseq hxK
  refine ⟨a, haK, ?_⟩
  exact LocalVelocityBlowup.of_sequence (t ∘ φ) (x ∘ φ)
    (fun n => ht (φ n)) (htend.comp hφ.tendsto_atTop) hxend
    (hlarge.comp hφ.tendsto_atTop)

end MethbokeAddon.FeffermanFamily
