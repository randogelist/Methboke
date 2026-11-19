import QuasiFeffermanB.RootContract
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Actual smooth gluing of a finite initial NSE pair and a classical QFB tail.

The input front states the literal physical equations, regularity and initial
value on the half-open finite cylinder. The other input is the original
ClassicalTail. Equality of both velocity and normalized pressure on their
open overlap is explicit; obtaining these equalities is a separate theorem.

The output is constructed by a piecewise splice. Its GlobalSmoothNSE fields
are proved from local equality with the supplied physical pairs. No solution,
continuation or gluing conclusion is hidden in a certificate field.

Prepared source only; matching external cached verification is pending.
No local Lean execution. This source is staged outside Material discovery.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB
open scoped ContDiff Topology

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

def initialFrontSpacetime (T : ℝ) : Set (ℝ × Vec) :=
  {z | 0 ≤ z.1 ∧ z.1 < T}

/-- A literal finite initial classical pair, with smoothness up to time zero.
Existence of this pair is an explicit input, not inferred from smooth data.
-/
structure InitialClassicalFront (ν T : ℝ) (a : Field)
    (u : Velocity) (p : Pressure) : Prop where
  velocity_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime T)
  pressure_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) (initialFrontSpacetime T)
  velocity_periodic : ∀ t ∈ Ico (0 : ℝ) T, SpatialPeriodic (u t)
  pressure_periodic : ∀ t ∈ Ico (0 : ℝ) T, SpatialPeriodic (p t)
  divergence_free : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
      ν • laplacian (u t) x
  initial : u 0 = a
  velocity_mean_zero : ∀ t ∈ Ico (0 : ℝ) T, MeanZero (u t)
  pressure_mean_zero : ∀ t ∈ Ico (0 : ℝ) T, PressureMeanZero (p t)

def finiteCapSplice {E : Type*} (η : ℝ) (f g : ℝ → E) : ℝ → E :=
  fun t => if t < η then f t else g t

theorem finiteCapSplice_eventually_left {E : Type*}
    (η : ℝ) (f g : ℝ → E) {t : ℝ} (ht : t < η) :
    finiteCapSplice η f g =ᶠ[𝓝 t] f := by
  filter_upwards [Iio_mem_nhds ht] with r hr
  simp only [finiteCapSplice, if_pos hr]

/-- On the overlap and to its right the splice is locally the tail, including
at the joining time. The conclusion is a neighborhood equality of functions.
-/
theorem finiteCapSplice_eventually_right {E : Type*}
    (δ T η : ℝ) (f g : ℝ → E) (hηT : η < T)
    (hagree : ∀ r ∈ Ioo δ T, f r = g r) {t : ℝ} (ht : δ < t) :
    finiteCapSplice η f g =ᶠ[𝓝 t] g := by
  filter_upwards [Ioi_mem_nhds ht] with r hr
  by_cases h : r < η
  · simpa only [finiteCapSplice, if_pos h] using hagree r ⟨hr, h.trans hηT⟩
  · simp only [finiteCapSplice, if_neg h]

private theorem finiteCapSplice_timeDerivative_congr
    {f g : Velocity} {t : ℝ} (h : f =ᶠ[𝓝 t] g) (x : Vec) :
    timeDerivative f t x = timeDerivative g t x := by
  have hx : (fun r => f r x) =ᶠ[𝓝 t] (fun r => g r x) := by
    filter_upwards [h] with r hr
    exact congrFun hr x
  exact hx.derivWithin_eq_of_nhds

/-- Smoothness of the actual splice on the closed nonnegative-time cylinder.
At zero the proof uses within-set smoothness from the finite initial front;
at the join it uses the open overlap and genuine tail smoothness.
-/
theorem finiteCapSplice_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ T η : ℝ) (f g : ℝ → Vec → E) (hδη : δ < η) (hηT : η < T)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) (initialFrontSpacetime T))
    (hg : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => g z.1 z.2) (tailSpacetime δ))
    (hagree : ∀ r ∈ Ioo δ T, f r = g r) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => finiteCapSplice η f g z.1 z.2)
      forwardSpacetime := by
  intro z hz
  by_cases hleft : z.1 < η
  · have hzT : z.1 < T := hleft.trans hηT
    have htime : ∀ᶠ y : ℝ × Vec in 𝓝 z, y.1 < T :=
      (continuous_fst.tendsto z).eventually (Iio_mem_nhds hzT)
    have hlocal : initialFrontSpacetime T ∈ 𝓝[forwardSpacetime] z := by
      filter_upwards [self_mem_nhdsWithin, htime.filter_mono nhdsWithin_le_nhds]
        with y hy hyT
      exact ⟨hy, hyT⟩
    have hbase : ContDiffWithinAt ℝ ∞ (fun y : ℝ × Vec => f y.1 y.2)
        forwardSpacetime z :=
      (hf z ⟨hz, hzT⟩).mono_of_mem_nhdsWithin hlocal
    have heq : (fun y : ℝ × Vec => finiteCapSplice η f g y.1 y.2) =ᶠ[𝓝 z]
        (fun y : ℝ × Vec => f y.1 y.2) := by
      filter_upwards [(continuous_fst.tendsto z).eventually
        (finiteCapSplice_eventually_left η f g hleft)] with y hy
      exact congrFun hy y.2
    exact hbase.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds)
      heq.self_of_nhds
  · have hδz : δ < z.1 := hδη.trans_le (le_of_not_gt hleft)
    have htime : ∀ᶠ y : ℝ × Vec in 𝓝 z, δ < y.1 :=
      (continuous_fst.tendsto z).eventually (Ioi_mem_nhds hδz)
    have hlocal : tailSpacetime δ ∈ 𝓝[forwardSpacetime] z := by
      filter_upwards [htime.filter_mono nhdsWithin_le_nhds] with y hy
      exact hy.le
    have hbase : ContDiffWithinAt ℝ ∞ (fun y : ℝ × Vec => g y.1 y.2)
        forwardSpacetime z :=
      (hg z hδz.le).mono_of_mem_nhdsWithin hlocal
    have heq : (fun y : ℝ × Vec => finiteCapSplice η f g y.1 y.2) =ᶠ[𝓝 z]
        (fun y : ℝ × Vec => g y.1 y.2) := by
      filter_upwards [(continuous_fst.tendsto z).eventually
        (finiteCapSplice_eventually_right δ T η f g hηT hagree hδz)] with y hy
      exact congrFun hy y.2
    exact hbase.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds)
      heq.self_of_nhds

/-- Every field of GlobalSmoothNSE is proved for the constructed splice.
The overlap equalities concern the actual physical velocity and pressure.
-/
theorem finite_cap_splice_global_smooth
    (ν T δ η : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (H : InitialClassicalFront ν T a u p) (K : ClassicalTail ν δ v q)
    (hη0 : 0 < η) (hδη : δ < η) (hηT : η < T)
    (huv : ∀ r ∈ Ioo δ T, u r = v r)
    (hpq : ∀ r ∈ Ioo δ T, p r = q r) :
    GlobalSmoothNSE ν a (finiteCapSplice η u v) (finiteCapSplice η p q) := by
  have hleft (t : ℝ) (ht : t < η) : finiteCapSplice η u v t = u t :=
    (finiteCapSplice_eventually_left η u v ht).self_of_nhds
  have hleftp (t : ℝ) (ht : t < η) : finiteCapSplice η p q t = p t :=
    (finiteCapSplice_eventually_left η p q ht).self_of_nhds
  have hright (t : ℝ) (ht : δ < t) : finiteCapSplice η u v t = v t :=
    (finiteCapSplice_eventually_right δ T η u v hηT huv ht).self_of_nhds
  have hrightp (t : ℝ) (ht : δ < t) : finiteCapSplice η p q t = q t :=
    (finiteCapSplice_eventually_right δ T η p q hηT hpq ht).self_of_nhds
  refine {
    velocity_smooth := finiteCapSplice_contDiffOn δ T η u v hδη hηT
      H.velocity_smooth K.velocity_smooth huv
    pressure_smooth := finiteCapSplice_contDiffOn δ T η p q hδη hηT
      H.pressure_smooth K.pressure_smooth hpq
    velocity_periodic := ?_
    pressure_periodic := ?_
    divergence_free := ?_
    equation := ?_
    initial := ?_
    velocity_mean_zero := ?_
    pressure_mean_zero := ?_
  }
  · intro t ht
    by_cases h : t < η
    · rw [hleft t h]
      exact H.velocity_periodic t ⟨ht, h.trans hηT⟩
    · have hδt := hδη.trans_le (le_of_not_gt h)
      rw [hright t hδt]
      exact K.velocity_periodic t hδt.le
  · intro t ht
    by_cases h : t < η
    · rw [hleftp t h]
      exact H.pressure_periodic t ⟨ht, h.trans hηT⟩
    · have hδt := hδη.trans_le (le_of_not_gt h)
      rw [hrightp t hδt]
      exact K.pressure_periodic t hδt.le
  · intro t ht x
    by_cases h : t < η
    · rw [hleft t h]
      exact H.divergence_free t ⟨ht, h.trans hηT⟩ x
    · have hδt := hδη.trans_le (le_of_not_gt h)
      rw [hright t hδt]
      exact K.divergence_free t hδt.le x
  · intro t ht x
    by_cases h : t < η
    · rw [finiteCapSplice_timeDerivative_congr
        (finiteCapSplice_eventually_left η u v h) x, hleft t h, hleftp t h]
      exact H.equation t ⟨ht, h.trans hηT⟩ x
    · have hδt := hδη.trans_le (le_of_not_gt h)
      rw [finiteCapSplice_timeDerivative_congr
        (finiteCapSplice_eventually_right δ T η u v hηT huv hδt) x,
        hright t hδt, hrightp t hδt]
      exact K.equation t hδt.le x
  · rw [hleft 0 hη0]
    exact H.initial
  · intro t ht
    by_cases h : t < η
    · rw [hleft t h]
      exact H.velocity_mean_zero t ⟨ht, h.trans hηT⟩
    · have hδt := hδη.trans_le (le_of_not_gt h)
      rw [hright t hδt]
      exact K.velocity_mean_zero t hδt.le
  · intro t ht
    by_cases h : t < η
    · rw [hleftp t h]
      exact H.pressure_mean_zero t ⟨ht, h.trans hηT⟩
    · have hδt := hδη.trans_le (le_of_not_gt h)
      rw [hrightp t hδt]
      exact K.pressure_mean_zero t hδt.le

/-- Choose the joining time strictly inside the overlap. The resulting global
pair retains the whole original finite front and agrees with the supplied tail
from the joining time onward.
-/
theorem finite_cap_gluing
    (ν T δ : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (H : InitialClassicalFront ν T a u p) (K : ClassicalTail ν δ v q)
    (hδ0 : 0 ≤ δ) (hδT : δ < T)
    (huv : ∀ r ∈ Ioo δ T, u r = v r)
    (hpq : ∀ r ∈ Ioo δ T, p r = q r) :
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      (∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r) ∧
      ∀ r : ℝ, (δ + T) / 2 ≤ r → U r = v r ∧ P r = q r := by
  let η : ℝ := (δ + T) / 2
  have hη0 : 0 < η := by dsimp [η]; linarith
  have hδη : δ < η := by dsimp [η]; linarith
  have hηT : η < T := by dsimp [η]; linarith
  refine ⟨finiteCapSplice η u v, finiteCapSplice η p q,
    finite_cap_splice_global_smooth ν T δ η a u v p q H K hη0 hδη hηT huv hpq, ?_, ?_⟩
  · intro r hr
    by_cases h : r < η
    · constructor <;> simp only [finiteCapSplice, if_pos h]
    · have hδr : δ < r := hδη.trans_le (le_of_not_gt h)
      simpa only [finiteCapSplice, if_neg h] using
        And.intro (huv r ⟨hδr, hr.2⟩).symm (hpq r ⟨hδr, hr.2⟩).symm
  · intro r hr
    have h : ¬ r < η := not_lt_of_ge hr
    constructor <;> simp only [finiteCapSplice, if_neg h]

end

end MethbokeAddon.WeakFouriermanB
