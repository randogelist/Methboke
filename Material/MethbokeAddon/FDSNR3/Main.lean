import MethbokeAddon.FDSNR3.PhysicalFamily
import MethbokeAddon.FDSNR3.CorrectionAdmission
import MethbokeAddon.FDSNR3.LocalizedSeed
import MethbokeAddon.FDSNR3.CrossingTimePhase
import MethbokeAddon.FDSNR3.FrequencyCutoff
import MethbokeAddon.FDSNR3.TranslationRigidity

/-!
# The canonical whole-space FDSN construction

The only premise is the original physical Seed. A nonzero Fourier region,
its separated active and untouched subregions, the signed compact time
phase, the actual real inverse Fourier correction, and the native residual
are all constructed here. One tuple supplies every clause of Family.

Prepared without local Lean execution. The exact root requires matching
external cached compilation and independent literal type/axiom evidence.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure Metric
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

/-- Every admitted whole-space seed has the canonical five-clause family,
with the same initial data, pressure, terminal tail, helical powers, and
energy/dissipation histories. The force is the actual native residual. -/
theorem FDSN_R3 {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (hseed : Seed ν T u p F) : Family ν T u p F := by
  classical
  intro s hs
  obtain ⟨tstar, htstar, i, c, r, hc, hr, haway, hball⟩ :=
    hseed.exists_nonzero_fourier_ball_after hs
  let a : ℝ := (s + tstar) / 2
  let b : ℝ := (tstar + T) / 2
  have hsa : s < a := by dsimp [a]; linarith [htstar.1]
  have hat : a < tstar := by dsimp [a]; linarith [htstar.1]
  have htb : tstar < b := by dsimp [b]; linarith [htstar.2]
  have hbT : b < T := by dsimp [b]; linarith [htstar.2]
  have ha : 0 < a := lt_of_le_of_lt hs.1 hsa
  have hab : a < b := hat.trans htb
  have htstar0 : tstar ∈ Ioo (0 : ℝ) T := ⟨ha.trans hat, htstar.2⟩
  have htstar1 : tstar ∈ Ico (0 : ℝ) T := ⟨htstar0.1.le, htstar0.2⟩
  obtain ⟨ψ, anchor, δ, ρ, hδ, hρ, hψ, hcψ, ho, hψbound,
      hactiveBall, hanchorBall, hdisjoint, hactiveOne, hanchorZero,
      hlow, hzeroFrequency⟩ := exists_odd_frequency_cutoff hr haway
  have hcstar : fourierVelocity (u tstar) c i ≠ 0 :=
    hball c (Metric.mem_ball_self hr)
  have hψc : ψ c = 1 :=
    hactiveOne c (Metric.mem_closedBall_self hδ.le)
  have hct : ContinuousAt (fun t : ℝ => fourierVelocity (u t) c i) tstar :=
    (EuclideanSpace.proj i : CVec →L[ℂ] ℂ).continuous.continuousAt.comp
      (hseed.local_schwartz.continuousAt_fourier_time htstar0 c)
  obtain ⟨tzero, β, slope, htzero, hneTime, hczero, hβ, hcβ,
      hβab, hβstar, hβzero, hβderiv, hslope⟩ :=
    exists_signed_crossing_time_phase hat htb hct hcstar
  have hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T := by
    intro t ht
    exact ⟨ha.trans (hβab ht).1, (hβab ht).2.trans hbT⟩
  have hSpos : tsupport β ⊆ Ioi (0 : ℝ) :=
    fun _ ht => (hβsupport ht).1
  have htzero0 : tzero ∈ Ioo (0 : ℝ) T :=
    ⟨ha.trans htzero.1, htzero.2.trans hbT⟩
  let H : 𝓢(FamilySpacetime, Vec) :=
    jointPhysicalCorrection hseed.local_schwartz hβ hcβ hβsupport hψ hcψ
  have hH0 : ∀ z : ℝ × Vec, H (0, z) = 0 :=
    jointPhysicalCorrection_zero_parameter hseed.local_schwartz
      hβ hcβ hβsupport hψ hcψ
  have hHsupport : ∀ lam : ℝ,
      tsupport (schwartzFamilyVelocity H lam) ⊆ tsupport β :=
    physicalPhaseCorrection_tsupport_subset hseed.local_schwartz
      hβ hcβ hβsupport hψ hcψ
  obtain ⟨χ, hχ, hcχ, hχsupport, hχone⟩ := exists_timeCutoff_for_interval ha hab hbT
  let B : ℝ × Vec → Vec := fun z => localizedSeed χ u z.1 z.2
  have hB : Function.HasTemperateGrowth B :=
    hseed.local_schwartz.hasTemperateGrowth_localizedSeed hχ hcχ hχsupport
  have hBseed : ∀ t ∈ tsupport β, ∀ x : Vec, B (t, x) = u t x := by
    intro t ht x
    have hχt : χ t = 1 :=
      (hχone t ⟨(hβab ht).1.le, (hβab ht).2.le⟩).eq_of_nhds
    exact congrFun (localizedSeed_eq_of_eq_one u hχt) x
  let J : 𝓢(FamilySpacetime, Vec) := jointResidualSchwartz ν B hB H
  have hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x :=
    jointResidualSchwartz_eq_original ν u B hB H (tsupport β) hSpos hHsupport hBseed
  have hJ0 : ∀ z : ℝ × Vec, J (0, z) = 0 :=
    schwartzResidual_zero_parameter ν u H J hnative hH0
  let U : ℝ → Velocity := correctedVelocity u H
  let G : ℝ → Velocity := correctedForce F J
  have hU : U = physicalPhaseFamily hseed.local_schwartz hβ hcβ hβsupport hψ hcψ := rfl
  have hhistory : EnergyDissipationPreservation T (Real.pi / 4) u U := by
    intro lam hlam t ht
    rw [hU]
    exact ⟨physicalPhaseFamily_energy hseed.local_schwartz hβ hcβ hβsupport
        hψ hcψ ho hlam.le ht,
      physicalPhaseFamily_dissipation hseed.local_schwartz hβ hcβ hβsupport
        hψ hcψ ho hlam.le ht⟩
  have hdiv : ∀ lam : ℝ, |lam| < Real.pi / 4 →
      ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (U lam t) x = 0 := by
    intro lam hlam t ht
    rw [hU]
    exact physicalPhaseFamily_divergence_free hseed.local_schwartz
      hseed.front.divergence_free hβ hcβ hβsupport hψ hcψ ho hlam.le ht
  have henergy : ∀ lam : ℝ, |lam| < Real.pi / 4 → ∀ t ∈ Ico (0 : ℝ) T,
      Integrable (fun x : Vec => ‖U lam t x‖ ^ 2) volume := by
    intro lam hlam t ht
    rw [hU]
    exact physicalPhaseFamily_integrable_norm_sq hseed.local_schwartz
      hβ hcβ hβsupport hψ hcψ hlam.le ht
  have hdissipation : ∀ lam : ℝ, |lam| < Real.pi / 4 → ∀ t ∈ Ico (0 : ℝ) T,
      Integrable (gradientSquare (U lam t)) volume := by
    intro lam hlam t ht
    rw [hU]
    exact physicalPhaseFamily_gradientSquare_integrable hseed.local_schwartz
      hβ hcβ hβsupport hψ hcψ hlam.le ht
  have hrealization : ExactRealizationAndAgreement ν T a b (Real.pi / 4) u p F U G :=
    exactRealizationAndAgreement_of_schwartz_residual hseed ha hab hbT H J
      (tsupport β) hcβ.isCompact hβab hHsupport hnative hdiv henergy hdissipation hhistory
  have hpowers : CompleteHelicalPowerPreservation T (Real.pi / 4) u U := by
    constructor
    · intro lam hlam t ht ξ hξ σ
      rw [hU]
      exact physicalPhaseFamily_helicalPower hseed.local_schwartz
        hβ hcβ hβsupport hψ hcψ ho hlam.le ht ξ σ
    · refine ⟨ρ, hρ, ?_⟩
      intro lam hlam t ht ξ hξ
      rw [hU]
      exact fourierVelocity_physicalPhaseFamily_eq_of_cutoff_zero
        hseed.local_schwartz hβ hcβ hβsupport hψ hcψ ho hlam.le ht (hlow ξ hξ)
  have htranslation : TranslationSeparation tstar (Real.pi / 4) U := by
    apply translationSeparation_of_actual_packet_fourier U β ψ
      (fourierVelocity (u tstar)) tstar hβstar i c anchor hδ hψc hcstar
    · intro ξ hξ
      have hclosed : ξ ∈ closedBall anchor δ := ball_subset_closedBall hξ
      exact ⟨hanchorZero ξ hclosed, hball ξ (hanchorBall hclosed)⟩
    · intro lam hlam ξ
      rw [hU]
      exact fourierVelocity_physicalPhaseFamily hseed.local_schwartz
        hβ hcβ hβsupport hψ hcψ ho hlam.le htstar1 ξ
  have hforce : PhysicalProjectedForceSeparation T (Real.pi / 4) G := by
    have hraw := physicalProjectedForceSeparation_inversePhaseCorrection
      ν T (Real.pi / 4) tzero slope u F hseed.local_schwartz hβ ψ hψ hcψ ho
      htzero0 hβderiv hβzero hslope
      (hseed.front.divergence_free tzero ⟨htzero0.1.le, htzero0.2⟩)
      (by simpa only [hψc] using (one_ne_zero : (1 : ℝ) ≠ 0)) hczero
    have hG : ∀ lam : ℝ, |lam| < Real.pi / 4 →
        G lam = MethbokeAddon.FDSN.residualForce ν u F
          (inversePhaseCorrection β ψ lam u) := by
      intro lam hlam
      change correctedForce F J lam = _
      rw [correctedForce_eq_native_residual ν u F H J hnative lam]
      have hcorrection : schwartzFamilyVelocity H lam = inversePhaseCorrection β ψ lam u :=
        physicalPhaseCorrection_eq_inversePhaseCorrection hseed.local_schwartz
          hβ hcβ hβsupport hψ hcψ hlam.le
      rw [hcorrection]
    intro lam eta hlam heta hne
    rw [hG lam hlam, hG eta heta]
    exact hraw lam eta hlam heta hne
  refine ⟨a, b, tstar, Real.pi / 4, U, G, hsa, hat, htb, hbT, rfl,
    correctedVelocity_zero u H hH0, correctedForce_zero F J hJ0,
    (correctedVelocity_joint_correction_smooth u H).contDiffOn,
    (correctedForce_joint_correction_smooth F J).contDiffOn,
    commonTemporalSupport_of_schwartz_residual ν a b (Real.pi / 4) u F H J
      (tsupport β) hcβ.isCompact hβab hHsupport hnative,
    hrealization, hpowers, htranslation, hforce,
    weightedSmoothSmallness_corrected (Real.pi / 4) u F H J hH0 hJ0, hhistory⟩

end

end MethbokeAddon.FDSNR3
