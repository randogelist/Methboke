import FDSNR3CorrectionAdmission.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff SchwartzMap Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

example (u : Velocity) (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) :
    correctedVelocity u H lam = u + schwartzFamilyVelocity H lam := rfl

example (F : Velocity) (J : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) :
    correctedForce F J lam = F + schwartzFamilyVelocity J lam := rfl

example (u : Velocity)
    (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) :
    correctedVelocity u H lam - u = schwartzFamilyVelocity H lam := by
  exact MethbokeAddon.FDSNR3.correctedVelocity_sub u H lam

example (F : Velocity)
    (J : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) :
    correctedForce F J lam - F = schwartzFamilyVelocity J lam := by
  exact MethbokeAddon.FDSNR3.correctedForce_sub F J lam

example (u : Velocity) (H : 𝓢(FamilySpacetime, Vec))
    (hzero : ∀ z : ℝ × Vec, H (0, z) = 0) : correctedVelocity u H 0 = u := by
  exact MethbokeAddon.FDSNR3.correctedVelocity_zero u H hzero

example (F : Velocity) (J : 𝓢(FamilySpacetime, Vec))
    (hzero : ∀ z : ℝ × Vec, J (0, z) = 0) : correctedForce F J 0 = F := by
  exact MethbokeAddon.FDSNR3.correctedForce_zero F J hzero

example (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec => schwartzFamilyVelocity H lam z.1 z.2) := by
  exact MethbokeAddon.FDSNR3.schwartzFamilyVelocity_smooth H lam

example (u : Velocity)
    (H : 𝓢(FamilySpacetime, Vec)) :
    ContDiff ℝ ∞ (fun q : FamilySpacetime =>
      (correctedVelocity u H q.1 - u) q.2.1 q.2.2) := by
  exact MethbokeAddon.FDSNR3.correctedVelocity_joint_correction_smooth u H

example (F : Velocity)
    (J : 𝓢(FamilySpacetime, Vec)) :
    ContDiff ℝ ∞ (fun q : FamilySpacetime =>
      (correctedForce F J q.1 - F) q.2.1 q.2.2) := by
  exact MethbokeAddon.FDSNR3.correctedForce_joint_correction_smooth F J

example (u : Velocity)
    (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) {t : ℝ}
    (ht : t ∉ tsupport (schwartzFamilyVelocity H lam)) :
    correctedVelocity u H lam t = u t := by
  exact MethbokeAddon.FDSNR3.correctedVelocity_eq_of_notMem_timeSupport u H lam ht

example (F : Velocity)
    (J : 𝓢(FamilySpacetime, Vec)) (lam : ℝ) {t : ℝ}
    (ht : t ∉ tsupport (schwartzFamilyVelocity J lam)) :
    correctedForce F J lam t = F t := by
  exact MethbokeAddon.FDSNR3.correctedForce_eq_of_notMem_timeSupport F J lam ht

example
    {a b : ℝ} (H : 𝓢(FamilySpacetime, Vec)) (lam : ℝ)
    {S : Set ℝ} (hS : IsCompact S) (hSab : S ⊆ Ioo a b)
    (hsupp : tsupport (schwartzFamilyVelocity H lam) ⊆ S) :
    CompactTemporalCorrection a b (schwartzFamilyVelocity H lam) := by
  exact MethbokeAddon.FDSNR3.compactTemporalCorrection_of_jointSchwartz H lam hS hSab hsupp

example
    (ν : ℝ) (u : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x)
    (lam : ℝ) :
    schwartzFamilyVelocity J lam =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) := by
  exact MethbokeAddon.FDSNR3.schwartzFamilyVelocity_eq_native_residual ν u H J hnative lam

example
    (ν : ℝ) (u : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x)
    (lam : ℝ) :
    tsupport (schwartzFamilyVelocity J lam) ⊆
      tsupport (schwartzFamilyVelocity H lam) := by
  exact MethbokeAddon.FDSNR3.schwartzResidual_timeSupport_subset ν u H J hnative lam

example
    (ν : ℝ) (u : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x)
    (hzero : ∀ z : ℝ × Vec, H (0, z) = 0) :
    ∀ z : ℝ × Vec, J (0, z) = 0 := by
  exact MethbokeAddon.FDSNR3.schwartzResidual_zero_parameter ν u H J hnative hzero

example
    (ν : ℝ) (u F : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x)
    (lam : ℝ) :
    correctedForce F J lam =
      MethbokeAddon.FDSN.residualForce ν u F (schwartzFamilyVelocity H lam) := by
  exact MethbokeAddon.FDSNR3.correctedForce_eq_native_residual ν u F H J hnative lam

example
    (ν a b ε : ℝ) (u F : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (S : Set ℝ) (hS : IsCompact S) (hSab : S ⊆ Ioo a b)
    (hsupp : ∀ lam : ℝ, tsupport (schwartzFamilyVelocity H lam) ⊆ S)
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x) :
    CommonTemporalSupport a b ε u F (correctedVelocity u H) (correctedForce F J) := by
  exact MethbokeAddon.FDSNR3.commonTemporalSupport_of_schwartz_residual ν a b ε u F H J S hS hSab hsupp hnative

example
    (ε : ℝ) (u F : Velocity) (H J : 𝓢(FamilySpacetime, Vec))
    (hH0 : ∀ z : ℝ × Vec, H (0, z) = 0)
    (hJ0 : ∀ z : ℝ × Vec, J (0, z) = 0) :
    WeightedSmoothSmallness ε u F (correctedVelocity u H) (correctedForce F J) := by
  exact MethbokeAddon.FDSNR3.weightedSmoothSmallness_corrected ε u F H J hH0 hJ0

example
    {ν T a b ε : ℝ} {u F : Velocity} {p : Pressure}
    (hseed : Seed ν T u p F) (ha : 0 < a) (hab : a < b) (hbT : b < T)
    (H J : 𝓢(FamilySpacetime, Vec))
    (S : Set ℝ) (hS : IsCompact S) (hSab : S ⊆ Ioo a b)
    (hsupp : ∀ lam : ℝ, tsupport (schwartzFamilyVelocity H lam) ⊆ S)
    (hnative : ∀ lam t : ℝ, ∀ x : Vec, J (lam, (t, x)) =
      MethbokeAddon.FDSN.residualForce ν u 0 (schwartzFamilyVelocity H lam) t x)
    (hdiv : ∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
      divergence (correctedVelocity u H lam t) x = 0)
    (henergy : ∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T,
      Integrable (fun x : Vec => ‖correctedVelocity u H lam t x‖ ^ 2) volume)
    (hdissipation : ∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T,
      Integrable (gradientSquare (correctedVelocity u H lam t)) volume)
    (hhistory : EnergyDissipationPreservation T ε u (correctedVelocity u H)) :
    ExactRealizationAndAgreement ν T a b ε u p F
      (correctedVelocity u H) (correctedForce F J) := by
  exact MethbokeAddon.FDSNR3.exactRealizationAndAgreement_of_schwartz_residual hseed ha hab hbT H J S hS hSab hsupp hnative hdiv henergy hdissipation hhistory

end

end MethbokeAddon.FDSNR3

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedVelocity"
#check @MethbokeAddon.FDSNR3.correctedVelocity
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedVelocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedVelocity"
#print axioms MethbokeAddon.FDSNR3.correctedVelocity
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedVelocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedForce"
#check @MethbokeAddon.FDSNR3.correctedForce
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedForce"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedForce"
#print axioms MethbokeAddon.FDSNR3.correctedForce
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedForce"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedVelocity_sub"
#check @MethbokeAddon.FDSNR3.correctedVelocity_sub
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedVelocity_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedVelocity_sub"
#print axioms MethbokeAddon.FDSNR3.correctedVelocity_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedVelocity_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedForce_sub"
#check @MethbokeAddon.FDSNR3.correctedForce_sub
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedForce_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedForce_sub"
#print axioms MethbokeAddon.FDSNR3.correctedForce_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedForce_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedVelocity_zero"
#check @MethbokeAddon.FDSNR3.correctedVelocity_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedVelocity_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedVelocity_zero"
#print axioms MethbokeAddon.FDSNR3.correctedVelocity_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedVelocity_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedForce_zero"
#check @MethbokeAddon.FDSNR3.correctedForce_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedForce_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedForce_zero"
#print axioms MethbokeAddon.FDSNR3.correctedForce_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedForce_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzFamilyVelocity_smooth"
#check @MethbokeAddon.FDSNR3.schwartzFamilyVelocity_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzFamilyVelocity_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzFamilyVelocity_smooth"
#print axioms MethbokeAddon.FDSNR3.schwartzFamilyVelocity_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzFamilyVelocity_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedVelocity_joint_correction_smooth"
#check @MethbokeAddon.FDSNR3.correctedVelocity_joint_correction_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedVelocity_joint_correction_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedVelocity_joint_correction_smooth"
#print axioms MethbokeAddon.FDSNR3.correctedVelocity_joint_correction_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedVelocity_joint_correction_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedForce_joint_correction_smooth"
#check @MethbokeAddon.FDSNR3.correctedForce_joint_correction_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedForce_joint_correction_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedForce_joint_correction_smooth"
#print axioms MethbokeAddon.FDSNR3.correctedForce_joint_correction_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedForce_joint_correction_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedVelocity_eq_of_notMem_timeSupport"
#check @MethbokeAddon.FDSNR3.correctedVelocity_eq_of_notMem_timeSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedVelocity_eq_of_notMem_timeSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedVelocity_eq_of_notMem_timeSupport"
#print axioms MethbokeAddon.FDSNR3.correctedVelocity_eq_of_notMem_timeSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedVelocity_eq_of_notMem_timeSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedForce_eq_of_notMem_timeSupport"
#check @MethbokeAddon.FDSNR3.correctedForce_eq_of_notMem_timeSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedForce_eq_of_notMem_timeSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedForce_eq_of_notMem_timeSupport"
#print axioms MethbokeAddon.FDSNR3.correctedForce_eq_of_notMem_timeSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedForce_eq_of_notMem_timeSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.compactTemporalCorrection_of_jointSchwartz"
#check @MethbokeAddon.FDSNR3.compactTemporalCorrection_of_jointSchwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.compactTemporalCorrection_of_jointSchwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.compactTemporalCorrection_of_jointSchwartz"
#print axioms MethbokeAddon.FDSNR3.compactTemporalCorrection_of_jointSchwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.compactTemporalCorrection_of_jointSchwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzFamilyVelocity_eq_native_residual"
#check @MethbokeAddon.FDSNR3.schwartzFamilyVelocity_eq_native_residual
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzFamilyVelocity_eq_native_residual"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzFamilyVelocity_eq_native_residual"
#print axioms MethbokeAddon.FDSNR3.schwartzFamilyVelocity_eq_native_residual
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzFamilyVelocity_eq_native_residual"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzResidual_timeSupport_subset"
#check @MethbokeAddon.FDSNR3.schwartzResidual_timeSupport_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzResidual_timeSupport_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzResidual_timeSupport_subset"
#print axioms MethbokeAddon.FDSNR3.schwartzResidual_timeSupport_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzResidual_timeSupport_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzResidual_zero_parameter"
#check @MethbokeAddon.FDSNR3.schwartzResidual_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzResidual_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzResidual_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.schwartzResidual_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzResidual_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.correctedForce_eq_native_residual"
#check @MethbokeAddon.FDSNR3.correctedForce_eq_native_residual
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.correctedForce_eq_native_residual"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.correctedForce_eq_native_residual"
#print axioms MethbokeAddon.FDSNR3.correctedForce_eq_native_residual
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.correctedForce_eq_native_residual"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.commonTemporalSupport_of_schwartz_residual"
#check @MethbokeAddon.FDSNR3.commonTemporalSupport_of_schwartz_residual
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.commonTemporalSupport_of_schwartz_residual"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.commonTemporalSupport_of_schwartz_residual"
#print axioms MethbokeAddon.FDSNR3.commonTemporalSupport_of_schwartz_residual
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.commonTemporalSupport_of_schwartz_residual"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.weightedSmoothSmallness_corrected"
#check @MethbokeAddon.FDSNR3.weightedSmoothSmallness_corrected
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.weightedSmoothSmallness_corrected"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.weightedSmoothSmallness_corrected"
#print axioms MethbokeAddon.FDSNR3.weightedSmoothSmallness_corrected
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.weightedSmoothSmallness_corrected"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.exactRealizationAndAgreement_of_schwartz_residual"
#check @MethbokeAddon.FDSNR3.exactRealizationAndAgreement_of_schwartz_residual
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.exactRealizationAndAgreement_of_schwartz_residual"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.exactRealizationAndAgreement_of_schwartz_residual"
#print axioms MethbokeAddon.FDSNR3.exactRealizationAndAgreement_of_schwartz_residual
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.exactRealizationAndAgreement_of_schwartz_residual"

