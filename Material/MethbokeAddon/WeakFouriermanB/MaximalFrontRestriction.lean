import MethbokeAddon.WeakFouriermanB.MaximalClassicalFront

/-!
# Restriction to a half-open horizon at or below the maximal lifetime

The terminal time is excluded from InitialClassicalFront. Every point of its
cylinder therefore lies strictly inside a shorter admitted front. Local
smoothness and the literal physical fields transfer from that shorter front,
even when the chosen finite horizon equals the maximal lifetime.

No value, trace or regularity at a finite maximal endpoint is asserted.
Prepared source only; matching external cached compilation and fresh
exact-type/axiom audits are required. No local Lean ran.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open scoped ContDiff ENNReal Topology

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- A finite half-open restriction may reach the maximal lifetime itself,
because every time at which a physical field is required is strictly earlier.
-/
theorem maximal_classical_front_restrict_le
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (H : MaximalClassicalFront ν a u p Tmax) (hT : 0 < T)
    (hTmax : ENNReal.ofReal T ≤ Tmax) :
    InitialClassicalFront ν T a u p := by
  have hlocal (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
      ∃ S : ℝ, t ∈ Ico (0 : ℝ) S ∧ InitialClassicalFront ν S a u p := by
    let S : ℝ := (t + T) / 2
    have hS : 0 < S := by dsimp only [S]; linarith [ht.1]
    have htS : t < S := by dsimp only [S]; linarith [ht.2]
    have hST : S < T := by dsimp only [S]; linarith [ht.2]
    have hSmax : ENNReal.ofReal S < Tmax :=
      ((ENNReal.ofReal_lt_ofReal_iff_of_nonneg hS.le).mpr hST).trans_le hTmax
    exact ⟨S, ⟨ht.1, htS⟩, H.finite_front S hS hSmax⟩
  have hwindow (z : ℝ × Vec) (S : ℝ) (hzS : z.1 < S) :
      initialFrontSpacetime S ∈ 𝓝[initialFrontSpacetime T] z := by
    have htime : ∀ᶠ y : ℝ × Vec in 𝓝 z, y.1 < S :=
      (continuous_fst.tendsto z).eventually (Iio_mem_nhds hzS)
    filter_upwards [self_mem_nhdsWithin, htime.filter_mono nhdsWithin_le_nhds]
      with y hy hyS
    exact ⟨hy.1, hyS⟩
  refine {
    velocity_smooth := ?_
    pressure_smooth := ?_
    velocity_periodic := ?_
    pressure_periodic := ?_
    divergence_free := ?_
    equation := ?_
    initial := H.initial
    velocity_mean_zero := ?_
    pressure_mean_zero := ?_
  }
  · intro z hz
    obtain ⟨S, hzS, HS⟩ := hlocal z.1 hz
    exact (HS.velocity_smooth z hzS).mono_of_mem_nhdsWithin (hwindow z S hzS.2)
  · intro z hz
    obtain ⟨S, hzS, HS⟩ := hlocal z.1 hz
    exact (HS.pressure_smooth z hzS).mono_of_mem_nhdsWithin (hwindow z S hzS.2)
  · intro t ht
    obtain ⟨S, htS, HS⟩ := hlocal t ht
    exact HS.velocity_periodic t htS
  · intro t ht
    obtain ⟨S, htS, HS⟩ := hlocal t ht
    exact HS.pressure_periodic t htS
  · intro t ht x
    obtain ⟨S, htS, HS⟩ := hlocal t ht
    exact HS.divergence_free t htS x
  · intro t ht x
    obtain ⟨S, htS, HS⟩ := hlocal t ht
    exact HS.equation t htS x
  · intro t ht
    obtain ⟨S, htS, HS⟩ := hlocal t ht
    exact HS.velocity_mean_zero t htS
  · intro t ht
    obtain ⟨S, htS, HS⟩ := hlocal t ht
    exact HS.pressure_mean_zero t htS

end
end MethbokeAddon.WeakFouriermanB
