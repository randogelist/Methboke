import MethbokeAddon.FDSN.ActiveTriad
import MethbokeAddon.FDSN.FamilyRealization
import MethbokeAddon.FDSN.LocalizedPairSeparation
import MethbokeAddon.FDSN.LocalizedForceSeparation
import MethbokeAddon.FDSN.TimeBump

/-!
# FDSN: the one seed-conditional periodic spectral nonrigidity theorem

This assembly selects one actual active triad, one output Fourier pair,
one common time interval, one normalized bump, and one velocity/force
family. Every canonical clause then applies to those same witnesses.

The construction preserves every complex-linear modal-observation norm,
so its stronger array theorem explicitly specializes to every genuine
orthonormal helical frame in the canonical unparameterized `Family`.

This file is a source candidate. External compilation and a matching named
axiom audit, not preparation of this text, determine its verification tier.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.FDSN

noncomputable section

/-- The stronger construction is independent of any frame assumptions. -/
theorem Seed.familyFor {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) (frame : HelicalFrameArray) :
    FamilyFor frame ν T u p F := by
  intro s hs
  obtain ⟨t, ht, hactive⟩ := h.exists_active_noncollinear_triad_after s hs
  have ht0 : t ∈ Ico (0 : ℝ) T := ⟨(hs.1.trans ht.1.le), ht.2⟩
  obtain ⟨k, hk, i, hcoeff, hseparate⟩ :=
    h.active_triad_separation_data t ht0 hactive
  let a : ℝ := (s + t) / 2
  let b : ℝ := (t + T) / 2
  have hsa : s < a := by dsimp [a]; linarith [ht.1]
  have hat : a < t := by dsimp [a]; linarith [ht.1]
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have hab : a < b := hat.trans htb
  have ha0 : 0 < a := lt_of_le_of_lt hs.1 hsa
  obtain ⟨β, hβ, hβc, hβI, hβt, hβbounds⟩ :=
    exists_normalized_time_bump hat htb
  have hβ0 : tsupport β ⊆ Ioo (0 : ℝ) T := by
    intro r hr
    exact ⟨ha0.trans (hβI hr).1, (hβI hr).2.trans hbT⟩
  have hβa : a ∉ tsupport β := by
    intro ha
    exact (lt_irrefl a) (hβI ha).1
  refine ⟨a, b, t, Real.pi / 4,
    localizedPairVelocity k β u, localizedPairForce ν k β u F,
    hsa, hab, hbT, ⟨hat, htb⟩, by positivity,
    localizedPairVelocity_zero_parameter k β u,
    localizedPairForce_zero_parameter ν k β u F, ?_,
    (localizedPairForceCorrection_joint_smooth h k hβ hβ0).contDiffOn,
    localizedPair_exactRealization h hk hβ hβc hβ0 a b (Real.pi / 4) hbT hβI,
    localizedPairVelocity_helicalPower h frame hk β (Real.pi / 4), ?_,
    localizedPairForce_projectedSeparation h hk hβ hβc hβ0
      a t ha0 hat.le ht.2 hβa hβt i hcoeff,
    localizedPair_family_smallness h k hβ hβ0 a b (Real.pi / 4) hab.le⟩
  · simpa only [localizedPairVelocity_sub_eq_correction] using
      (localizedPairCorrection_joint_smooth h k hβ hβ0).contDiffOn
  · intro lambda η hlambda hη hlambdaη
    exact (hseparate β hβt lambda η hlambda hη hlambdaη).2

/-- Canonical FDSN: every admitted periodic seed generates the one common
family satisfying exact realization, helical powers, translation separation,
projected-force separation, and smooth smallness in every final interval. -/
theorem FEFFERMAN_D_SPECTRAL_NONRIGIDITY
    (ν T : ℝ) (u : Velocity) (p : Pressure) (F : Velocity) :
    Seed ν T u p F → Family ν T u p F := by
  intro h
  exact family_of_all_frame_arrays (fun frame => h.familyFor frame)

theorem FDSN (ν T : ℝ) (u : Velocity) (p : Pressure) (F : Velocity) :
    Seed ν T u p F → Family ν T u p F :=
  FEFFERMAN_D_SPECTRAL_NONRIGIDITY ν T u p F

/-- Explicit specialization of the canonical endpoint to the genuine fixed
helical frame used in a presentation of the theorem. -/
theorem FEFFERMAN_D_SPECTRAL_NONRIGIDITY_fixed_frame
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (hseed : Seed ν T u p F)
    {frame : HelicalFrameArray} (hframe : IsHelicalFrame frame) :
    FamilyFor frame ν T u p F :=
  (FEFFERMAN_D_SPECTRAL_NONRIGIDITY ν T u p F hseed).for_fixed_helical_frame hframe

end

end MethbokeAddon.FDSN
