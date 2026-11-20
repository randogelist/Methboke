import MethbokeAddon.WeakFouriermanB.FiniteCapGluing
import MethbokeAddon.WeakFouriermanB.LocalFront

/-!
Actual time translation of an initial classical NSE front. The right
derivative at the new initial time is obtained from ordinary differentiability
at an interior old time. Translation by zero is treated separately.

These lemmas only translate supplied physical solutions; they do not assert
local existence or a lifespan. Matching external cached verification is required.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB
open scoped ContDiff Topology

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

theorem initial_front_time_hasDerivAt
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    HasDerivAt (fun r : ℝ => u r x) (timeDerivative u t x) t := by
  have hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (localFrontSpacetime T) := H.velocity_smooth.mono (by
    intro z hz
    exact ⟨hz.1.le, hz.2⟩)
  exact local_time_hasDerivAt u T hu t ht x

theorem initial_front_timeDerivative_translate
    (ν T s : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hs : 0 ≤ s)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (T - s)) (x : Vec) :
    timeDerivative (fun r => u (s + r)) t x = timeDerivative u (s + t) x := by
  rcases eq_or_lt_of_le hs with hs0 | hspos
  · subst s
    simp only [zero_add]
  · have hst : s + t ∈ Ioo (0 : ℝ) T := by
      constructor <;> linarith [ht.1, ht.2]
    have hd := initial_front_time_hasDerivAt ν T a u p H (s + t) hst x
    have hc : HasDerivAt (fun r : ℝ => u (s + r) x)
        (timeDerivative u (s + t) x) t := by
      simpa only [Function.comp_def, id_eq, one_smul] using
        hd.scomp t ((hasDerivAt_id t).const_add s)
    exact hc.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Ici 0) t ht.1)

theorem initial_front_time_translate
    (ν T s : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hs : 0 ≤ s) :
    InitialClassicalFront ν (T - s) (u s)
      (fun t => u (s + t)) (fun t => p (s + t)) := by
  have htime (t : ℝ) (ht : t ∈ Ico (0 : ℝ) (T - s)) :
      s + t ∈ Ico (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2]
  have hmap : MapsTo (fun z : ℝ × Vec => (s + z.1, z.2))
      (initialFrontSpacetime (T - s)) (initialFrontSpacetime T) := by
    intro z hz
    exact htime z.1 hz
  have hc : ContDiff ℝ ∞ (fun z : ℝ × Vec => (s + z.1, z.2)) :=
    (contDiff_const.add contDiff_fst).prodMk contDiff_snd
  refine {
    velocity_smooth := H.velocity_smooth.comp hc.contDiffOn hmap
    pressure_smooth := H.pressure_smooth.comp hc.contDiffOn hmap
    velocity_periodic := fun t ht => H.velocity_periodic (s + t) (htime t ht)
    pressure_periodic := fun t ht => H.pressure_periodic (s + t) (htime t ht)
    divergence_free := fun t ht => H.divergence_free (s + t) (htime t ht)
    equation := ?_
    initial := by simp only [add_zero]
    velocity_mean_zero := fun t ht => H.velocity_mean_zero (s + t) (htime t ht)
    pressure_mean_zero := fun t ht => H.pressure_mean_zero (s + t) (htime t ht)
  }
  intro t ht x
  rw [initial_front_timeDerivative_translate ν T s a u p H hs t ht x]
  exact H.equation (s + t) (htime t ht) x

/-- The backwards shift is used only strictly after its new origin. This
keeps both the original and shifted derivatives at interior positive times.
-/
theorem initial_front_timeDerivative_shift_back
    (ν T s : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hs : 0 ≤ s)
    (t : ℝ) (ht : t ∈ Ioo s (s + T)) (x : Vec) :
    timeDerivative (fun r => u (r - s)) t x = timeDerivative u (t - s) x := by
  have hts : t - s ∈ Ioo (0 : ℝ) T := by
    constructor <;> linarith [ht.1, ht.2]
  have hd := initial_front_time_hasDerivAt ν T a u p H (t - s) hts x
  have hc : HasDerivAt (fun r : ℝ => u (r - s) x)
      (timeDerivative u (t - s) x) t := by
    simpa only [Function.comp_def, id_eq, one_smul] using
      hd.scomp t ((hasDerivAt_id t).sub_const s)
  exact hc.hasDerivWithinAt.derivWithin
    ((uniqueDiffOn_Ici 0) t (le_trans hs (le_of_lt ht.1)))

theorem initial_front_shift_back_equation
    (ν T s : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hs : 0 ≤ s)
    (t : ℝ) (ht : t ∈ Ioo s (s + T)) (x : Vec) :
    timeDerivative (fun r => u (r - s)) t x + convection (u (t - s)) x +
      SingularClosure.gradient (p (t - s)) x = ν • laplacian (u (t - s)) x := by
  rw [initial_front_timeDerivative_shift_back ν T s a u p H hs t ht x]
  apply H.equation
  constructor <;> linarith [ht.1, ht.2]

end

end MethbokeAddon.WeakFouriermanB
