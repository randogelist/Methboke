import MethbokeAddon.FDSNR3.SliceSchwartz
import MethbokeAddon.FDSN.JointResidual

/-!
# Whole-space admission and native residual realization

These closure lemmas use the literal weighted-jet predicates and native
Navier--Stokes operators. In particular, the time-zero equation is preserved
by the correction's vanishing germ, with the native right derivative retained.
The Fourier construction and its rapid-decay estimates are separate inputs
to these assembly lemmas; none is encoded in the Seed contract.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

theorem weightedJet_add_le (N n : ℕ) (u v : Velocity)
    (hu : ContDiff ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2))
    (hv : ContDiff ℝ ∞ (fun z : ℝ × Vec => v z.1 z.2)) (z : ℝ × Vec) :
    weightedJet N n (u + v) z ≤ weightedJet N n u z + weightedJet N n v z := by
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have heq : (fun y : ℝ × Vec => (u + v) y.1 y.2) =
      (fun y : ℝ × Vec => u y.1 y.2) + (fun y : ℝ × Vec => v y.1 y.2) := rfl
  unfold weightedJet
  rw [heq, iteratedFDeriv_add_apply (hu.of_le hn).contDiffAt (hv.of_le hn).contDiffAt]
  calc
    _ ≤ (1 + ‖z.2‖) ^ N *
        (‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => u y.1 y.2) z‖ +
          ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => v y.1 y.2) z‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
    _ = _ := by ring

theorem GlobalSchwartzBounds.add {u v : Velocity}
    (hu : GlobalSchwartzBounds u) (hv : GlobalSchwartzBounds v)
    (hus : ContDiff ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2))
    (hvs : ContDiff ℝ ∞ (fun z : ℝ × Vec => v z.1 z.2)) :
    GlobalSchwartzBounds (u + v) := by
  intro N n
  obtain ⟨A, hA, huA⟩ := hu N n
  obtain ⟨B, hB, hvB⟩ := hv N n
  exact ⟨A + B, add_nonneg hA hB, fun z =>
    (weightedJet_add_le N n u v hus hvs z).trans (add_le_add (huA z) (hvB z))⟩

theorem LocalSchwartz.of_global {T : ℝ} {v : Velocity}
    (hs : ContDiff ℝ ∞ (fun z : ℝ × Vec => v z.1 z.2))
    (hb : GlobalSchwartzBounds v) : LocalSchwartz T v := by
  refine ⟨hs.contDiffOn, ?_⟩
  intro b hbT N n
  obtain ⟨C, hC, hbound⟩ := hb N n
  refine ⟨C, hC, ?_⟩
  intro t ht x
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hmem : (t, x) ∈ preterminalSpacetime T :=
    ⟨ht.1, lt_of_le_of_lt ht.2 hbT.2⟩
  unfold weightedJetWithin
  rw [iteratedFDerivWithin_eq_iteratedFDeriv
    (uniqueDiffOn_preterminalSpacetime T) (hs.of_le hn).contDiffAt hmem]
  exact hbound (t, x)

theorem LocalSchwartz.add {T : ℝ} {u v : Velocity}
    (hu : LocalSchwartz T u) (hv : LocalSchwartz T v) :
    LocalSchwartz T (u + v) := by
  refine ⟨hu.1.add hv.1, ?_⟩
  intro b hb N n
  obtain ⟨A, hA, huA⟩ := hu.2 b hb N n
  obtain ⟨B, hB, hvB⟩ := hv.2 b hb N n
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro t ht x
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hz : (t, x) ∈ preterminalSpacetime T :=
    ⟨ht.1, lt_of_le_of_lt ht.2 hb.2⟩
  have heq : (fun y : ℝ × Vec => (u + v) y.1 y.2) =
      (fun y : ℝ × Vec => u y.1 y.2) + (fun y : ℝ × Vec => v y.1 y.2) := rfl
  have hjet : weightedJetWithin T N n (u + v) (t, x) ≤
      weightedJetWithin T N n u (t, x) + weightedJetWithin T N n v (t, x) := by
    unfold weightedJetWithin
    rw [heq, iteratedFDerivWithin_add_apply ((hu.1.of_le hn) _ hz)
      ((hv.1.of_le hn) _ hz) (uniqueDiffOn_preterminalSpacetime T) hz]
    calc
      _ ≤ (1 + ‖x‖) ^ N *
          (‖iteratedFDerivWithin ℝ n (fun y : ℝ × Vec => u y.1 y.2)
              (preterminalSpacetime T) (t, x)‖ +
            ‖iteratedFDerivWithin ℝ n (fun y : ℝ × Vec => v y.1 y.2)
              (preterminalSpacetime T) (t, x)‖) :=
        mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ = _ := by ring
  exact hjet.trans (add_le_add (huA t ht x) (hvB t ht x))

theorem LocalSchwartz.add_global {T : ℝ} {u h : Velocity}
    (hu : LocalSchwartz T u)
    (hs : ContDiff ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2))
    (hb : GlobalSchwartzBounds h) : LocalSchwartz T (u + h) :=
  hu.add (LocalSchwartz.of_global hs hb)

theorem AdmissibleForce.add {F G : Velocity}
    (hF : AdmissibleForce F) (hG : AdmissibleForce G) : AdmissibleForce (F + G) := by
  refine ⟨hF.smooth.add hG.smooth,
    hF.schwartz_bounds.add hG.schwartz_bounds hF.smooth hG.smooth, ?_⟩
  obtain ⟨a, b, ha, hab, hFzero⟩ := hF.time_support
  obtain ⟨c, d, hc, hcd, hGzero⟩ := hG.time_support
  refine ⟨min a c, max b d, lt_min ha hc, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (hab.trans_le (le_max_left _ _))
  · intro t ht
    have htF : t ∉ Icc a b := by
      intro h
      exact ht ⟨(min_le_left _ _).trans h.1, h.2.trans (le_max_left _ _)⟩
    have htG : t ∉ Icc c d := by
      intro h
      exact ht ⟨(min_le_right _ _).trans h.1, h.2.trans (le_max_right _ _)⟩
    change F t + G t = 0
    rw [hFzero t htF, hGzero t htG, zero_add]

theorem CompactTemporalCorrection.admissibleForce {a b : ℝ} {h : Velocity}
    (hh : CompactTemporalCorrection a b h) (ha : 0 < a) (hab : a < b) :
    AdmissibleForce h := by
  refine ⟨hh.1, hh.2.1, a, b, ha, hab, ?_⟩
  intro t ht
  apply image_eq_zero_of_notMem_tsupport
  intro hmem
  have hin := hh.2.2.2 hmem
  exact ht ⟨hin.1.le, hin.2.le⟩

/-- The existing domain-independent residual theorem realizes the actual
whole-space PDE, including the initial boundary. -/
theorem PreterminalNSE.add_residual
    {ν T : ℝ} {u h F : Velocity} {p : Pressure}
    (hu : PreterminalNSE ν T u p F)
    (hs : ContDiff ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2))
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (h t) x = 0) :
    PreterminalNSE ν T (u + h) p (MethbokeAddon.FDSN.residualForce ν u F h) := by
  refine ⟨hu.velocity_smooth.add hs.contDiffOn, hu.pressure_smooth, ?_, ?_⟩
  · intro t ht
    exact MethbokeAddon.FDSN.native_divergence_add_zero (u t) (h t)
      (preterminal_slice_smooth hu.velocity_smooth ht)
      (hs.comp (contDiff_const.prodMk contDiff_id)) (hu.divergence_free t ht) (hdiv t ht)
  · intro t ht x
    by_cases hmem : t ∈ tsupport h
    · have htime := hsupp hmem
      exact MethbokeAddon.FDSN.native_residual_momentum_on_open_slab ν u F h p 0 T
        (hu.velocity_smooth.mono (fun _ hq => ⟨hq.1.le, hq.2⟩)) hs.contDiffOn
        (fun r hr => hu.equation r ⟨hr.1.le, hr.2⟩) t htime x
    · have hz := MethbokeAddon.FDSN.velocity_zero_germ_of_notMem_timeSupport h hmem x
      have hvel : (fun z : ℝ × Vec => (u + h) z.1 z.2) =ᶠ[𝓝 (t, x)]
          (fun z => u z.1 z.2) := by
        filter_upwards [hz] with z hz
        change u z.1 z.2 + h z.1 z.2 = u z.1 z.2
        have hz0 : h z.1 z.2 = 0 := hz
        rw [hz0, add_zero]
      have hforce : (fun z : ℝ × Vec =>
          MethbokeAddon.FDSN.residualForce ν u F h z.1 z.2) =ᶠ[𝓝 (t, x)]
          (fun z => F z.1 z.2) := by
        filter_upwards [hz.eventuallyEq_nhds] with z hz
        exact MethbokeAddon.FDSN.residualForce_eq_of_zero_germ ν u F h z.1 z.2 hz
      exact (MethbokeAddon.FeffermanFamily.nativeForcedEquation_congr ν hvel
        Filter.EventuallyEq.rfl hforce).mpr (hu.equation t ht x)

theorem residualForce_eq_add_zero_force (ν : ℝ) (u F h : Velocity) :
    MethbokeAddon.FDSN.residualForce ν u F h =
      F + MethbokeAddon.FDSN.residualForce ν u 0 h := by
  funext t x
  simp only [MethbokeAddon.FDSN.residualForce, Pi.add_apply, Pi.zero_apply]
  abel

/-- Admission of the actual force reduces to the genuine correction bounds,
without imposing global regularity on the singular seed. -/
theorem admissibleForce_residual_of_correction
    {ν a b : ℝ} {u F h : Velocity} (hF : AdmissibleForce F)
    (hcorrection : CompactTemporalCorrection a b
      (MethbokeAddon.FDSN.residualForce ν u 0 h))
    (ha : 0 < a) (hab : a < b) :
    AdmissibleForce (MethbokeAddon.FDSN.residualForce ν u F h) := by
  rw [residualForce_eq_add_zero_force]
  exact hF.add (hcorrection.admissibleForce ha hab)

theorem BoundedEnergy.of_equal_history {T : ℝ} {u v : Velocity}
    (hu : BoundedEnergy T u)
    (hv : ∀ t ∈ Ico (0 : ℝ) T, Integrable (fun x : Vec => ‖v t x‖ ^ 2) volume)
    (heq : ∀ t ∈ Ico (0 : ℝ) T,
      (∫ x : Vec, ‖v t x‖ ^ 2) = ∫ x : Vec, ‖u t x‖ ^ 2) :
    BoundedEnergy T v := by
  obtain ⟨E, hE, hbound⟩ := hu
  refine ⟨E, hE, ?_⟩
  intro t ht
  exact ⟨hv t ht, (heq t ht).trans_le (hbound t ht).2⟩

theorem FiniteDissipation.of_equal_history {T : ℝ} {u v : Velocity}
    (hu : FiniteDissipation T u)
    (hv : ∀ t ∈ Ico (0 : ℝ) T, Integrable (gradientSquare (v t)) volume)
    (heq : ∀ t ∈ Ico (0 : ℝ) T, dissipation (v t) = dissipation (u t)) :
    FiniteDissipation T v := by
  refine ⟨hv, hu.2.congr_fun ?_ measurableSet_Ioo⟩
  intro t ht
  exact (heq t ⟨ht.1.le, ht.2⟩).symm

end

end MethbokeAddon.FDSNR3
