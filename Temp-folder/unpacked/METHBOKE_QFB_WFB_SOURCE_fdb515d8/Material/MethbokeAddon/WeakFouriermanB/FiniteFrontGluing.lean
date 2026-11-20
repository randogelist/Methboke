import MethbokeAddon.WeakFouriermanB.LocalClassicalUniqueness
import MethbokeAddon.WeakFouriermanB.LocalTimeTranslation

/-!
# Gluing a finite classical front to an actual finite restart

The second solution is given only on a finite interval measured from its own
initial time. It is translated to the old clock, and actual local uniqueness
proves both velocity and normalized-pressure agreement before the old endpoint.
The splice lies strictly inside that overlap. Its equation and smoothness are
proved locally, including the old initial boundary. No global tail or limiting
datum at the old endpoint is an input.

The restart's existence and duration remain explicit; this module does not
construct a uniform local lifespan. Prepared source, requiring matching
external cached compilation and fresh type/axiom audits. No local Lean ran.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff Topology

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Finite-to-finite smoothness of a splice. The later field is required only
on the open finite window `(δ,S)`, not on an infinite tail. -/
theorem finite_front_splice_contDiffOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ T S η : ℝ) (f g : ℝ → Vec → E) (hδη : δ < η) (hηT : η < T)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) (initialFrontSpacetime T))
    (hg : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => g z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ Ioo δ S})
    (hagree : ∀ r ∈ Ioo δ T, f r = g r) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => finiteCapSplice η f g z.1 z.2)
      (initialFrontSpacetime S) := by
  intro z hz
  by_cases hleft : z.1 < η
  · have hzT : z.1 < T := hleft.trans hηT
    have htime : ∀ᶠ y : ℝ × Vec in 𝓝 z, y.1 < T :=
      (continuous_fst.tendsto z).eventually (Iio_mem_nhds hzT)
    have hlocal : initialFrontSpacetime T ∈ 𝓝[initialFrontSpacetime S] z := by
      filter_upwards [self_mem_nhdsWithin, htime.filter_mono nhdsWithin_le_nhds]
        with y hy hyT
      exact ⟨hy.1, hyT⟩
    have hbase : ContDiffWithinAt ℝ ∞ (fun y : ℝ × Vec => f y.1 y.2)
        (initialFrontSpacetime S) z :=
      (hf z ⟨hz.1, hzT⟩).mono_of_mem_nhdsWithin hlocal
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
    have hlocal : {y : ℝ × Vec | y.1 ∈ Ioo δ S} ∈
        𝓝[initialFrontSpacetime S] z := by
      filter_upwards [self_mem_nhdsWithin, htime.filter_mono nhdsWithin_le_nhds]
        with y hy hyδ
      exact ⟨hyδ, hy.2⟩
    have hbase : ContDiffWithinAt ℝ ∞ (fun y : ℝ × Vec => g y.1 y.2)
        (initialFrontSpacetime S) z :=
      (hg z ⟨hδz, hz.2⟩).mono_of_mem_nhdsWithin hlocal
    have heq : (fun y : ℝ × Vec => finiteCapSplice η f g y.1 y.2) =ᶠ[𝓝 z]
        (fun y : ℝ × Vec => g y.1 y.2) := by
      filter_upwards [(continuous_fst.tendsto z).eventually
        (finiteCapSplice_eventually_right δ T η f g hηT hagree hδz)] with y hy
      exact congrFun hy y.2
    exact hbase.congr_of_eventuallyEq (heq.filter_mono nhdsWithin_le_nhds)
      heq.self_of_nhds

private theorem finiteFrontSplice_timeDerivative_congr
    {f g : Velocity} {t : ℝ} (h : f =ᶠ[𝓝 t] g) (x : Vec) :
    timeDerivative f t x = timeDerivative g t x := by
  have hx : (fun r => f r x) =ᶠ[𝓝 t] (fun r => g r x) := by
    filter_upwards [h] with r hr
    exact congrFun hr x
  exact hx.derivWithin_eq_of_nhds

/-- A supplied restart whose duration reaches beyond the old endpoint gives
an actual longer initial classical front. The constructed pair preserves the
entire old velocity and pressure, and agrees with the translated restart from
an interior joining time onward. No endpoint limit or global tail is assumed. -/
theorem initial_front_extend_from_restart
    (ν T s h : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (hν : 0 < ν) (H : InitialClassicalFront ν T a u p)
    (hs : s ∈ Ico (0 : ℝ) T) (hh : 0 < h)
    (K : InitialClassicalFront ν h (u s) v q) (hextend : T < s + h) :
    ∃ (U : Velocity) (P : Pressure), InitialClassicalFront ν (s + h) a U P ∧
      (∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r) ∧
      ∀ r ∈ Ico ((s + T) / 2) (s + h),
        U r = v (r - s) ∧ P r = q (r - s) := by
  let V : Velocity := fun r => v (r - s)
  let Q : Pressure := fun r => q (r - s)
  let η : ℝ := (s + T) / 2
  have hη0 : 0 < η := by dsimp [η]; linarith [hs.1, hs.2]
  have hsη : s < η := by dsimp [η]; linarith [hs.2]
  have hηT : η < T := by dsimp [η]; linarith [hs.2]
  have hrestart := initial_classical_front_unique ν (T - s) h (u s)
    (fun r => u (s + r)) v (fun r => p (s + r)) q hν (sub_pos.mpr hs.2) hh
    (initial_front_time_translate ν T s a u p H hs.1) K
  have hagree : ∀ r ∈ Ioo s T, u r = V r ∧ p r = Q r := by
    intro r hr
    have htime : r - s ∈ Ico (0 : ℝ) (min (T - s) h) := by
      constructor
      · linarith [hr.1]
      · apply lt_min <;> linarith [hr.2]
    have hc : s + (r - s) = r := by ring
    simpa only [V, Q, hc] using hrestart (r - s) htime
  have huv : ∀ r ∈ Ioo s T, u r = V r := fun r hr => (hagree r hr).1
  have hpq : ∀ r ∈ Ioo s T, p r = Q r := fun r hr => (hagree r hr).2
  have htime (r : ℝ) (hr : r ∈ Ioo s (s + h)) :
      r - s ∈ Ico (0 : ℝ) h := by
    constructor <;> linarith [hr.1, hr.2]
  have hmap : MapsTo (fun z : ℝ × Vec => (z.1 - s, z.2))
      {z : ℝ × Vec | z.1 ∈ Ioo s (s + h)} (initialFrontSpacetime h) := by
    intro z hz
    exact htime z.1 hz
  have hc : ContDiff ℝ ∞ (fun z : ℝ × Vec => (z.1 - s, z.2)) :=
    (contDiff_fst.sub contDiff_const).prodMk contDiff_snd
  have hVsmooth : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => V z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ Ioo s (s + h)} :=
    K.velocity_smooth.comp hc.contDiffOn hmap
  have hQsmooth : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => Q z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ Ioo s (s + h)} :=
    K.pressure_smooth.comp hc.contDiffOn hmap
  have hleft (r : ℝ) (hr : r < η) : finiteCapSplice η u V r = u r :=
    (finiteCapSplice_eventually_left η u V hr).self_of_nhds
  have hleftp (r : ℝ) (hr : r < η) : finiteCapSplice η p Q r = p r :=
    (finiteCapSplice_eventually_left η p Q hr).self_of_nhds
  have hright (r : ℝ) (hr : s < r) : finiteCapSplice η u V r = V r :=
    (finiteCapSplice_eventually_right s T η u V hηT huv hr).self_of_nhds
  have hrightp (r : ℝ) (hr : s < r) : finiteCapSplice η p Q r = Q r :=
    (finiteCapSplice_eventually_right s T η p Q hηT hpq hr).self_of_nhds
  have hfront : InitialClassicalFront ν (s + h) a
      (finiteCapSplice η u V) (finiteCapSplice η p Q) := by
    refine {
      velocity_smooth := finite_front_splice_contDiffOn s T (s + h) η u V hsη hηT
        H.velocity_smooth hVsmooth huv
      pressure_smooth := finite_front_splice_contDiffOn s T (s + h) η p Q hsη hηT
        H.pressure_smooth hQsmooth hpq
      velocity_periodic := ?_
      pressure_periodic := ?_
      divergence_free := ?_
      equation := ?_
      initial := ?_
      velocity_mean_zero := ?_
      pressure_mean_zero := ?_
    }
    · intro r hr
      by_cases hleft' : r < η
      · rw [hleft r hleft']
        exact H.velocity_periodic r ⟨hr.1, hleft'.trans hηT⟩
      · have hsr := hsη.trans_le (le_of_not_gt hleft')
        rw [hright r hsr]
        exact K.velocity_periodic (r - s) (htime r ⟨hsr, hr.2⟩)
    · intro r hr
      by_cases hleft' : r < η
      · rw [hleftp r hleft']
        exact H.pressure_periodic r ⟨hr.1, hleft'.trans hηT⟩
      · have hsr := hsη.trans_le (le_of_not_gt hleft')
        rw [hrightp r hsr]
        exact K.pressure_periodic (r - s) (htime r ⟨hsr, hr.2⟩)
    · intro r hr x
      by_cases hleft' : r < η
      · rw [hleft r hleft']
        exact H.divergence_free r ⟨hr.1, hleft'.trans hηT⟩ x
      · have hsr := hsη.trans_le (le_of_not_gt hleft')
        rw [hright r hsr]
        exact K.divergence_free (r - s) (htime r ⟨hsr, hr.2⟩) x
    · intro r hr x
      by_cases hleft' : r < η
      · rw [finiteFrontSplice_timeDerivative_congr
          (finiteCapSplice_eventually_left η u V hleft') x,
          hleft r hleft', hleftp r hleft']
        exact H.equation r ⟨hr.1, hleft'.trans hηT⟩ x
      · have hsr := hsη.trans_le (le_of_not_gt hleft')
        rw [finiteFrontSplice_timeDerivative_congr
          (finiteCapSplice_eventually_right s T η u V hηT huv hsr) x,
          hright r hsr, hrightp r hsr]
        exact initial_front_shift_back_equation ν h s (u s) v q K hs.1 r ⟨hsr, hr.2⟩ x
    · rw [hleft 0 hη0]
      exact H.initial
    · intro r hr
      by_cases hleft' : r < η
      · rw [hleft r hleft']
        exact H.velocity_mean_zero r ⟨hr.1, hleft'.trans hηT⟩
      · have hsr := hsη.trans_le (le_of_not_gt hleft')
        rw [hright r hsr]
        exact K.velocity_mean_zero (r - s) (htime r ⟨hsr, hr.2⟩)
    · intro r hr
      by_cases hleft' : r < η
      · rw [hleftp r hleft']
        exact H.pressure_mean_zero r ⟨hr.1, hleft'.trans hηT⟩
      · have hsr := hsη.trans_le (le_of_not_gt hleft')
        rw [hrightp r hsr]
        exact K.pressure_mean_zero (r - s) (htime r ⟨hsr, hr.2⟩)
  refine ⟨finiteCapSplice η u V, finiteCapSplice η p Q, hfront, ?_, ?_⟩
  · intro r hr
    by_cases hleft' : r < η
    · exact ⟨hleft r hleft', hleftp r hleft'⟩
    · have hsr := hsη.trans_le (le_of_not_gt hleft')
      exact ⟨(hright r hsr).trans (huv r ⟨hsr, hr.2⟩).symm,
        (hrightp r hsr).trans (hpq r ⟨hsr, hr.2⟩).symm⟩
  · intro r hr
    have hsr : s < r := hsη.trans_le hr.1
    exact ⟨hright r hsr, hrightp r hsr⟩

end
end MethbokeAddon.WeakFouriermanB
