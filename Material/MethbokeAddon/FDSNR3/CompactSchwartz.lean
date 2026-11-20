import MethbokeAddon.FDSNR3.Contracts
import Mathlib.Analysis.Calculus.TangentCone.Real
import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Admission from a fixed compact spatial carrier

This proves the actual local weighted mixed-derivative bounds, including
the right-hand initial boundary, from joint smoothness and a fixed compact
spatial carrier. It does not import or assume the existence of a singular seed.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open scoped ContDiff Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

theorem uniqueDiffOn_preterminalSpacetime (T : ℝ) :
    UniqueDiffOn ℝ (preterminalSpacetime T) := by
  have hset : preterminalSpacetime T = Ico (0 : ℝ) T ×ˢ (univ : Set Vec) := by
    ext z
    simp [preterminalSpacetime]
  rw [hset]
  exact (uniqueDiffOn_Ico (0 : ℝ) T).prod uniqueDiffOn_univ

/-- Every actual derivative within the preterminal domain vanishes outside
the closed spatial carrier. No differentiability premise is needed for
this locality statement. -/
theorem iteratedFDerivWithin_eq_zero_off_spatialCarrier
    {T : ℝ} {u : Velocity} {K : Set Vec} (hK : IsClosed K)
    (hcarrier : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, x ∉ K → u t x = 0)
    (n : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    {x : Vec} (hx : x ∉ K) :
    iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T) (t, x) = 0 := by
  have hnot : ∀ᶠ z : ℝ × Vec in 𝓝 (t, x), z.2 ∉ K :=
    (hK.isOpen_compl.preimage continuous_snd).mem_nhds hx
  have heq : (fun z : ℝ × Vec => u z.1 z.2) =ᶠ[
      𝓝[preterminalSpacetime T] (t, x)] (fun _ => (0 : Vec)) := by
    filter_upwards [hnot.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with z hz hzt
    exact hcarrier z.1 hzt z.2 hz
  simpa only [iteratedFDerivWithin_fun_zero, Pi.zero_apply] using
    heq.iteratedFDerivWithin_eq (hcarrier t ht x hx) n

theorem weightedJetWithin_eq_zero_off_spatialCarrier
    {T : ℝ} {u : Velocity} {K : Set Vec} (hK : IsClosed K)
    (hcarrier : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, x ∉ K → u t x = 0)
    (N n : ℕ) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T)
    {x : Vec} (hx : x ∉ K) : weightedJetWithin T N n u (t, x) = 0 := by
  simp only [weightedJetWithin,
    iteratedFDerivWithin_eq_zero_off_spatialCarrier hK hcarrier n ht hx,
    norm_zero, mul_zero]

/-- The R3-02 compact-carrier-to-local-Schwartz endpoint. Each derivative
order and spatial weight receives its own uniform bound on every regular
compact time slab; no uniform terminal-time bound is asserted. -/
theorem localSchwartz_of_compact_spatialCarrier
    {T : ℝ} {u : Velocity} {K : Set Vec} (hK : IsCompact K)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (hcarrier : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, x ∉ K → u t x = 0) :
    LocalSchwartz T u := by
  refine ⟨hu, ?_⟩
  intro b hb N n
  have hj : ContinuousOn
      (iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T)) (preterminalSpacetime T) :=
    hu.continuousOn_iteratedFDerivWithin (m := n)
      (by exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤))
      (uniqueDiffOn_preterminalSpacetime T)
  have hw : Continuous (fun z : ℝ × Vec => (1 + ‖z.2‖) ^ N) :=
    (continuous_const.add continuous_snd.norm).pow N
  have hjet : ContinuousOn (weightedJetWithin T N n u)
      (preterminalSpacetime T) := hw.continuousOn.mul hj.norm
  have hsubset : Icc (0 : ℝ) b ×ˢ K ⊆ preterminalSpacetime T := by
    intro z hz
    exact ⟨hz.1.1, lt_of_le_of_lt hz.1.2 hb.2⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn
    (hjet.mono hsubset)
  refine ⟨max 0 C, le_max_left _ _, ?_⟩
  intro t ht x
  by_cases hx : x ∈ K
  · calc
      weightedJetWithin T N n u (t, x)
          ≤ ‖weightedJetWithin T N n u (t, x)‖ := le_abs_self _
      _ ≤ C := hC (t, x) ⟨ht, hx⟩
      _ ≤ max 0 C := le_max_right _ _
  · rw [weightedJetWithin_eq_zero_off_spatialCarrier hK.isClosed hcarrier N n
      ⟨ht.1, lt_of_le_of_lt ht.2 hb.2⟩ hx]
    exact le_max_left _ _

end

end MethbokeAddon.FDSNR3
