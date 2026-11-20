import FDSNR3JointPacket.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

example : phaseParameterBump.rIn = Real.pi / 4 ∧
    phaseParameterBump.rOut = Real.pi / 2 := ⟨rfl, rfl⟩

example (lam : ℝ) : phaseParameterCutoff lam = phaseParameterBump lam := rfl

example : ContDiff ℝ ∞ phaseParameterCutoff := by
  apply MethbokeAddon.FDSNR3.phaseParameterCutoff_contDiff <;> assumption

example : HasCompactSupport phaseParameterCutoff := by
  apply MethbokeAddon.FDSNR3.phaseParameterCutoff_hasCompactSupport <;> assumption

example {lam : ℝ} (hlam : |lam| ≤ Real.pi / 4) :
    phaseParameterCutoff lam = 1 := by
  apply MethbokeAddon.FDSNR3.phaseParameterCutoff_eq_one <;> assumption

example (β : ℝ → ℝ) (ψ : Vec → ℝ) (u : Velocity) (z : (ℝ × ℝ) × Vec) :
    jointSpectralCorrection β ψ u z = phaseParameterCutoff z.1.1 •
      (packetPhaseIncrement β ψ z.1.1 z.1.2 z.2 • fourierVelocity (u z.1.2) z.2) := rfl

example 
    (β : ℝ → ℝ) (ψ : Vec → ℝ) (u : Velocity) (t : ℝ) (ξ : Vec) :
    jointSpectralCorrection β ψ u ((0, t), ξ) = 0 := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_zero_parameter <;> assumption

example 
    (β : ℝ → ℝ) (ψ : Vec → ℝ) (u : Velocity) {lam : ℝ}
    (hlam : phaseParameterCutoff lam = 0) (t : ℝ) (ξ : Vec) :
    jointSpectralCorrection β ψ u ((lam, t), ξ) = 0 := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_parameterCutoff_zero <;> assumption

example 
    {β : ℝ → ℝ} (ψ : Vec → ℝ) (u : Velocity) (lam : ℝ) {t : ℝ}
    (hβ : β t = 0) (ξ : Vec) :
    jointSpectralCorrection β ψ u ((lam, t), ξ) = 0 := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_beta_zero <;> assumption

example 
    (β : ℝ → ℝ) {ψ : Vec → ℝ} (u : Velocity) (lam t : ℝ) {ξ : Vec}
    (hψ : ψ ξ = 0) :
    jointSpectralCorrection β ψ u ((lam, t), ξ) = 0 := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_psi_zero <;> assumption

example 
    (β : ℝ → ℝ) (ψ : Vec → ℝ) (u : Velocity) {lam : ℝ}
    (hlam : |lam| ≤ Real.pi / 4) (t : ℝ) (ξ : Vec) :
    jointSpectralCorrection β ψ u ((lam, t), ξ) =
      packetPhaseIncrement β ψ lam t ξ • fourierVelocity (u t) ξ := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_on_small_parameter <;> assumption

example 
    {β : ℝ → ℝ} (ψ : Vec → ℝ) (u : Velocity) {J : Set ℝ}
    (hβsupport : tsupport β ⊆ J) (lam : ℝ) {t : ℝ} (ht : t ∉ J) (ξ : Vec) :
    jointSpectralCorrection β ψ u ((lam, t), ξ) = 0 := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_time_notMem <;> assumption

example 
    (β : ℝ → ℝ) (ψ : Vec → ℝ) (u : Velocity) :
    tsupport (jointSpectralCorrection β ψ u) ⊆
      (tsupport phaseParameterCutoff ×ˢ tsupport β) ×ˢ tsupport ψ := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_tsupport_subset <;> assumption

example 
    {β : ℝ → ℝ} {ψ : Vec → ℝ} (u : Velocity)
    (hβ : HasCompactSupport β) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (jointSpectralCorrection β ψ u) := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_hasCompactSupport <;> assumption

example 
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hψ : ContDiff ℝ ∞ ψ)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (jointSpectralCorrection β ψ u) := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_contDiff <;> assumption

example 
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψodd : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (ξ : Vec) (i : Fin 3) :
    jointSpectralCorrection β ψ u ((lam, t), -ξ) i =
      conj (jointSpectralCorrection β ψ u ((lam, t), ξ) i) := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_conjugacy <;> assumption

example 
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0)
    {β : ℝ → ℝ} (ψ : Vec → ℝ)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (lam t : ℝ) (ξ : Vec) :
    ∑ i : Fin 3, (ξ i : ℂ) * jointSpectralCorrection β ψ u ((lam, t), ξ) i = 0 := by
  apply MethbokeAddon.FDSNR3.jointSpectralCorrection_transverse <;> assumption

example {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ : ((ℝ × ℝ) × Vec) → CVec) =
      jointSpectralCorrection β ψ u := rfl

example 
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (z : (ℝ × ℝ) × Vec) :
    jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ z =
      jointSpectralCorrection β ψ u z := by
  apply MethbokeAddon.FDSNR3.jointSpectralSchwartz_apply <;> assumption

example 
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (t : ℝ) (ξ : Vec) :
    jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ ((0, t), ξ) = 0 := by
  apply MethbokeAddon.FDSNR3.jointSpectralSchwartz_zero_parameter <;> assumption

example 
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam : ℝ} (hlam : |lam| ≤ Real.pi / 4) (t : ℝ) (ξ : Vec) :
    jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ ((lam, t), ξ) =
      packetPhaseIncrement β ψ lam t ξ • fourierVelocity (u t) ξ := by
  apply MethbokeAddon.FDSNR3.jointSpectralSchwartz_eq_on_small_parameter <;> assumption

example 
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    tsupport (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ) ⊆
      (tsupport phaseParameterCutoff ×ˢ tsupport β) ×ˢ tsupport ψ := by
  apply MethbokeAddon.FDSNR3.jointSpectralSchwartz_tsupport_subset <;> assumption

end

end MethbokeAddon.FDSNR3

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseParameterBump"
#check @MethbokeAddon.FDSNR3.phaseParameterBump
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseParameterBump"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseParameterBump"
#print axioms MethbokeAddon.FDSNR3.phaseParameterBump
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseParameterBump"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseParameterCutoff"
#check @MethbokeAddon.FDSNR3.phaseParameterCutoff
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseParameterCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseParameterCutoff"
#print axioms MethbokeAddon.FDSNR3.phaseParameterCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseParameterCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseParameterCutoff_contDiff"
#check @MethbokeAddon.FDSNR3.phaseParameterCutoff_contDiff
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseParameterCutoff_contDiff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseParameterCutoff_contDiff"
#print axioms MethbokeAddon.FDSNR3.phaseParameterCutoff_contDiff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseParameterCutoff_contDiff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseParameterCutoff_hasCompactSupport"
#check @MethbokeAddon.FDSNR3.phaseParameterCutoff_hasCompactSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseParameterCutoff_hasCompactSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseParameterCutoff_hasCompactSupport"
#print axioms MethbokeAddon.FDSNR3.phaseParameterCutoff_hasCompactSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseParameterCutoff_hasCompactSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.phaseParameterCutoff_eq_one"
#check @MethbokeAddon.FDSNR3.phaseParameterCutoff_eq_one
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.phaseParameterCutoff_eq_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.phaseParameterCutoff_eq_one"
#print axioms MethbokeAddon.FDSNR3.phaseParameterCutoff_eq_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.phaseParameterCutoff_eq_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_zero_parameter"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_parameterCutoff_zero"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_parameterCutoff_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_parameterCutoff_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_parameterCutoff_zero"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_parameterCutoff_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_parameterCutoff_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_beta_zero"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_beta_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_beta_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_beta_zero"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_beta_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_beta_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_psi_zero"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_psi_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_psi_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_psi_zero"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_psi_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_psi_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_on_small_parameter"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_on_small_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_on_small_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_on_small_parameter"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_on_small_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_on_small_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_time_notMem"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_time_notMem
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_time_notMem"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_time_notMem"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_time_notMem
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_eq_zero_of_time_notMem"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_tsupport_subset"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_tsupport_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_tsupport_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_tsupport_subset"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_tsupport_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_tsupport_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_hasCompactSupport"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_hasCompactSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_hasCompactSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_hasCompactSupport"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_hasCompactSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_hasCompactSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_contDiff"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_contDiff
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_contDiff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_contDiff"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_contDiff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_contDiff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_conjugacy"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_conjugacy
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_conjugacy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_conjugacy"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_conjugacy
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_conjugacy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_transverse"
#check @MethbokeAddon.FDSNR3.jointSpectralCorrection_transverse
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_transverse"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralCorrection_transverse"
#print axioms MethbokeAddon.FDSNR3.jointSpectralCorrection_transverse
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralCorrection_transverse"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralSchwartz"
#check @MethbokeAddon.FDSNR3.jointSpectralSchwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralSchwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralSchwartz"
#print axioms MethbokeAddon.FDSNR3.jointSpectralSchwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralSchwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralSchwartz_apply"
#check @MethbokeAddon.FDSNR3.jointSpectralSchwartz_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralSchwartz_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralSchwartz_apply"
#print axioms MethbokeAddon.FDSNR3.jointSpectralSchwartz_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralSchwartz_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralSchwartz_zero_parameter"
#check @MethbokeAddon.FDSNR3.jointSpectralSchwartz_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralSchwartz_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralSchwartz_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.jointSpectralSchwartz_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralSchwartz_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralSchwartz_eq_on_small_parameter"
#check @MethbokeAddon.FDSNR3.jointSpectralSchwartz_eq_on_small_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralSchwartz_eq_on_small_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralSchwartz_eq_on_small_parameter"
#print axioms MethbokeAddon.FDSNR3.jointSpectralSchwartz_eq_on_small_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralSchwartz_eq_on_small_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointSpectralSchwartz_tsupport_subset"
#check @MethbokeAddon.FDSNR3.jointSpectralSchwartz_tsupport_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointSpectralSchwartz_tsupport_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointSpectralSchwartz_tsupport_subset"
#print axioms MethbokeAddon.FDSNR3.jointSpectralSchwartz_tsupport_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointSpectralSchwartz_tsupport_subset"

