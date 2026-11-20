import MethbokeAddon.WeakFouriermanB.InitialFrontAdmission
import MethbokeAddon.WeakFouriermanB.PressureUniqueness

/-!
# Uniqueness of supplied physical initial classical fronts

Both classical pairs are compared to one original Leray--Hopf trajectory
constructed from their common datum. The accepted finite-front comparison
gives equality at every positive time almost everywhere on the physical cube;
continuity and periodicity give pointwise equality. The literal NSE equations
then determine normalized pressure on the positive overlap, and continuity
extends pressure equality to time zero.

No local-existence or continuation premise is introduced. The inputs are
actual InitialClassicalFront witnesses. Prepared source; matching external
cached compilation and fresh exact-type/axiom audits are required. No local
Lean, Lake or kernel execution was used.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff Topology

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Restrict an actual initial classical front to a shorter horizon. -/
theorem initial_front_restrict
    (ν T S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p) (hST : S ≤ T) :
    InitialClassicalFront ν S a u p := by
  have hsub : initialFrontSpacetime S ⊆ initialFrontSpacetime T :=
    fun _ hz => ⟨hz.1, hz.2.trans_le hST⟩
  exact {
    velocity_smooth := H.velocity_smooth.mono hsub
    pressure_smooth := H.pressure_smooth.mono hsub
    velocity_periodic := fun t ht => H.velocity_periodic t ⟨ht.1, ht.2.trans_le hST⟩
    pressure_periodic := fun t ht => H.pressure_periodic t ⟨ht.1, ht.2.trans_le hST⟩
    divergence_free := fun t ht => H.divergence_free t ⟨ht.1, ht.2.trans_le hST⟩
    equation := fun t ht => H.equation t ⟨ht.1, ht.2.trans_le hST⟩
    initial := H.initial
    velocity_mean_zero := fun t ht => H.velocity_mean_zero t ⟨ht.1, ht.2.trans_le hST⟩
    pressure_mean_zero := fun t ht => H.pressure_mean_zero t ⟨ht.1, ht.2.trans_le hST⟩
  }

/-- An actual global smooth solution restricts to every finite initial front. -/
theorem global_smooth_to_initial_front
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : GlobalSmoothNSE ν a u p) : InitialClassicalFront ν T a u p := by
  exact {
    velocity_smooth := H.velocity_smooth.mono (fun _ hz => hz.1)
    pressure_smooth := H.pressure_smooth.mono (fun _ hz => hz.1)
    velocity_periodic := fun t ht => H.velocity_periodic t ht.1
    pressure_periodic := fun t ht => H.pressure_periodic t ht.1
    divergence_free := fun t ht => H.divergence_free t ht.1
    equation := fun t ht => H.equation t ht.1
    initial := H.initial
    velocity_mean_zero := fun t ht => H.velocity_mean_zero t ht.1
    pressure_mean_zero := fun t ht => H.pressure_mean_zero t ht.1
  }

/-- Equality on the initial half-open cylinder transports the entire physical
front, including the derivative within the nonnegative half-line at zero. -/
theorem initial_front_congr
    (ν T : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (H : InitialClassicalFront ν T a u p) (hT : 0 < T)
    (huv : ∀ r ∈ Ico (0 : ℝ) T, v r = u r)
    (hpq : ∀ r ∈ Ico (0 : ℝ) T, q r = p r) :
    InitialClassicalFront ν T a v q := by
  have htime (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) (x : Vec) :
      timeDerivative v t x = timeDerivative u t x := by
    have hTevent : ∀ᶠ r : ℝ in 𝓝[Ici (0 : ℝ)] t, r < T :=
      nhdsWithin_le_nhds (Iio_mem_nhds ht.2)
    have heq : (fun r => v r x) =ᶠ[𝓝[Ici (0 : ℝ)] t] (fun r => u r x) := by
      filter_upwards [self_mem_nhdsWithin, hTevent] with r hr hrT
      exact congrFun (huv r ⟨hr, hrT⟩) x
    exact heq.derivWithin_eq (congrFun (huv t ht) x)
  refine {
    velocity_smooth := H.velocity_smooth.congr (fun z hz => congrFun (huv z.1 hz) z.2)
    pressure_smooth := H.pressure_smooth.congr (fun z hz => congrFun (hpq z.1 hz) z.2)
    velocity_periodic := ?_
    pressure_periodic := ?_
    divergence_free := ?_
    equation := ?_
    initial := (huv 0 ⟨le_rfl, hT⟩).trans H.initial
    velocity_mean_zero := ?_
    pressure_mean_zero := ?_
  }
  · intro t ht
    rw [huv t ht]
    exact H.velocity_periodic t ht
  · intro t ht
    rw [hpq t ht]
    exact H.pressure_periodic t ht
  · intro t ht x
    rw [huv t ht]
    exact H.divergence_free t ht x
  · intro t ht x
    rw [htime t ht x, huv t ht, hpq t ht]
    exact H.equation t ht x
  · intro t ht
    rw [huv t ht]
    exact H.velocity_mean_zero t ht
  · intro t ht
    rw [hpq t ht]
    exact H.pressure_mean_zero t ht

private theorem continuousOn_Ico_eq_at_zero
    {E : Type*} [TopologicalSpace E] [T2Space E]
    {T : ℝ} (hT : 0 < T) {f g : ℝ → E}
    (hf : ContinuousOn f (Ico (0 : ℝ) T))
    (hg : ContinuousOn g (Ico (0 : ℝ) T))
    (heq : ∀ t ∈ Ioo (0 : ℝ) T, f t = g t) : f 0 = g 0 := by
  have hTevent : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), t < T :=
    nhdsWithin_le_nhds (Iio_mem_nhds hT)
  have hwindow : Ico (0 : ℝ) T ∈ 𝓝[>] (0 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin, hTevent] with t ht htT
    exact ⟨ht.le, htT⟩
  have hfilter : 𝓝[>] (0 : ℝ) ≤ 𝓝[Ico (0 : ℝ) T] (0 : ℝ) :=
    le_inf nhdsWithin_le_nhds (le_principal_iff.mpr hwindow)
  have hflim : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 (f 0)) :=
    (hf 0 ⟨le_rfl, hT⟩).mono_left hfilter
  have hglim : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (g 0)) :=
    (hg 0 ⟨le_rfl, hT⟩).mono_left hfilter
  have hevent : f =ᶠ[𝓝[>] (0 : ℝ)] g := by
    filter_upwards [self_mem_nhdsWithin, hTevent] with t ht htT
    exact heq t ⟨ht, htT⟩
  exact tendsto_nhds_unique hflim (hglim.congr' hevent.symm)

/-- Complete local classical uniqueness: two actual solutions with the same
datum agree in both velocity and normalized pressure on their entire common
half-open initial interval, including time zero. One fixed original weak path
is used for both comparisons. No arbitrary-data existence claim is made. -/
theorem initial_classical_front_unique
    (ν T S : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (hS : 0 < S)
    (H : InitialClassicalFront ν T a u p)
    (K : InitialClassicalFront ν S a v q) :
    ∀ r ∈ Ico (0 : ℝ) (min T S), u r = v r ∧ p r = q r := by
  have ha := initial_front_initial_smooth ν T a u p H hT
  obtain ⟨w, G, hw, _⟩ := smooth_datum_lerayHopf_exists ν hν a ha
  have hwu := initial_front_leray_hopf_identification ν T a u p w G H hν hT hw
  have hwv := initial_front_leray_hopf_identification ν S a v q w G K hν hS hw
  have htimeT (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (min T S)) :
      r ∈ Ico (0 : ℝ) T := ⟨hr.1.le, hr.2.trans_le (min_le_left T S)⟩
  have htimeS (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (min T S)) :
      r ∈ Ico (0 : ℝ) S := ⟨hr.1.le, hr.2.trans_le (min_le_right T S)⟩
  have huv : ∀ r ∈ Ioo (0 : ℝ) (min T S), u r = v r := by
    intro r hr
    exact continuous_periodic_field_eq_of_cube_ae
      (initial_front_smooth_slices ν T a u p H r (htimeT r hr)).smooth.continuous
      (initial_front_smooth_slices ν S a v q K r (htimeS r hr)).smooth.continuous
      (H.velocity_periodic r (htimeT r hr)) (K.velocity_periodic r (htimeS r hr))
      ((hwu r ⟨hr.1, (htimeT r hr).2⟩).symm.trans
        (hwv r ⟨hr.1, (htimeS r hr).2⟩))
  have hpq : ∀ r ∈ Ioo (0 : ℝ) (min T S), p r = q r := by
    apply normalized_pressure_eq_on_jointly_smooth_velocity_overlap isOpen_Ioo huv
    · intro r hr
      exact H.equation r (htimeT r hr)
    · intro r hr
      exact K.equation r (htimeS r hr)
    · exact H.pressure_smooth.mono (fun z hz => htimeT z.1 hz)
    · exact K.pressure_smooth.mono (fun z hz => htimeS z.1 hz)
    · intro r hr
      exact H.pressure_mean_zero r (htimeT r hr)
    · intro r hr
      exact K.pressure_mean_zero r (htimeS r hr)
  have hpq0 : p 0 = q 0 := by
    funext x
    apply continuousOn_Ico_eq_at_zero (lt_min hT hS)
      (f := fun r => p r x) (g := fun r => q r x)
    · exact H.pressure_smooth.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr.1, hr.2.trans_le (min_le_left T S)⟩)
    · exact K.pressure_smooth.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr.1, hr.2.trans_le (min_le_right T S)⟩)
    · intro r hr
      exact congrFun (hpq r hr) x
  intro r hr
  rcases eq_or_lt_of_le hr.1 with hzero | hpos
  · have hrzero : r = 0 := hzero.symm
    subst r
    exact ⟨H.initial.trans K.initial.symm, hpq0⟩
  · exact ⟨huv r ⟨hpos, hr.2⟩, hpq r ⟨hpos, hr.2⟩⟩

end
end MethbokeAddon.WeakFouriermanB
