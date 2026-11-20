import FDSNR3ForwardFourierSmooth.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

example :
    Function.HasTemperateGrowth (fun r : ℝ => (Real.fourierChar (-r) : ℂ)) := by
  apply MethbokeAddon.FDSNR3.fourierChar_neg_hasTemperateGrowth <;> assumption

example (q : ℝ × Vec) (x : Vec) : fourierSourceCLM (q, x) = (q.1, x) := rfl

example (q : ℝ × Vec) (x : Vec) :
    fourierSourceCLM (q, x) = (q.1, x) := by
  apply MethbokeAddon.FDSNR3.fourierSourceCLM_apply <;> assumption

example (z : (ℝ × Vec) × Vec) : jointFourierKernel z =
    (Real.fourierChar (-inner ℝ z.2 z.1.2) : ℂ) := rfl

example :
    Function.HasTemperateGrowth jointFourierKernel := by
  apply MethbokeAddon.FDSNR3.jointFourierKernel_hasTemperateGrowth <;> assumption

example (b R : ℝ) : fourierParameterBox b R =
    Ioo (0 : ℝ) b ×ˢ Metric.ball (0 : Vec) R := rfl

example (b R : ℝ) : IsOpen (fourierParameterBox b R) := by
  apply MethbokeAddon.FDSNR3.isOpen_fourierParameterBox <;> assumption

example {b R : ℝ} (hR : 0 < R)
    {q : ℝ × Vec} (hq : q ∈ fourierParameterBox b R) : ‖q‖ ≤ b + R := by
  apply MethbokeAddon.FDSNR3.norm_le_of_mem_fourierParameterBox <;> assumption

example (u : Velocity) (z : (ℝ × Vec) × Vec) : jointFourierIntegrand u z =
    jointFourierKernel z • complexify (u z.1.1 z.2) := rfl

example {T b R : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) :
    ContDiffOn ℝ ∞ (jointFourierIntegrand u) (fourierParameterBox b R ×ˢ univ) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_jointFourierIntegrand <;> assumption

example {T b R : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T)
    {q : ℝ × Vec} (hq : q ∈ fourierParameterBox b R) (x : Vec) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n
      (fun z : (ℝ × Vec) × Vec => complexify (u z.1.1 z.2))
      (fourierParameterBox b R ×ˢ univ) (q, x)‖ ≤
      ‖complexifyCLM‖ * ‖fourierSourceCLM‖ ^ n *
        ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
          (preterminalSpacetime T) (q.1, x)‖ := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.norm_fourier_source_jet_le <;> assumption

example (a : ℝ) (ha : 0 < a) (k m : ℕ) :
    a ^ k * a ^ (-((k + m : ℕ) : ℝ)) = a ^ (-(m : ℝ)) := by
  apply MethbokeAddon.FDSNR3.pow_mul_rpow_neg_add <;> assumption

example {T b R : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ fourierParameterBox b R, ∀ x : Vec,
      ‖iteratedFDerivWithin ℝ n (jointFourierIntegrand u)
        (fourierParameterBox b R ×ˢ univ) (q, x)‖ ≤
          C * (1 + ‖x‖) ^ (-((volume : Measure Vec).integrablePower : ℝ)) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.jointFourierIntegrand_jet_bound <;> assumption

example {T b R : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Vec => fourierVelocity (u q.1) q.2)
      (fourierParameterBox b R) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity_box <;> assumption

example {T : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Vec => fourierVelocity (u q.1) q.2)
      {q | q.1 ∈ Ioo (0 : ℝ) T} := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity <;> assumption

end

end MethbokeAddon.FDSNR3

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierChar_neg_hasTemperateGrowth"
#check @MethbokeAddon.FDSNR3.fourierChar_neg_hasTemperateGrowth
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierChar_neg_hasTemperateGrowth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierChar_neg_hasTemperateGrowth"
#print axioms MethbokeAddon.FDSNR3.fourierChar_neg_hasTemperateGrowth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierChar_neg_hasTemperateGrowth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierSourceCLM"
#check @MethbokeAddon.FDSNR3.fourierSourceCLM
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierSourceCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierSourceCLM"
#print axioms MethbokeAddon.FDSNR3.fourierSourceCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierSourceCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierSourceCLM_apply"
#check @MethbokeAddon.FDSNR3.fourierSourceCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierSourceCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierSourceCLM_apply"
#print axioms MethbokeAddon.FDSNR3.fourierSourceCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierSourceCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointFourierKernel"
#check @MethbokeAddon.FDSNR3.jointFourierKernel
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointFourierKernel"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointFourierKernel"
#print axioms MethbokeAddon.FDSNR3.jointFourierKernel
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointFourierKernel"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointFourierKernel_hasTemperateGrowth"
#check @MethbokeAddon.FDSNR3.jointFourierKernel_hasTemperateGrowth
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointFourierKernel_hasTemperateGrowth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointFourierKernel_hasTemperateGrowth"
#print axioms MethbokeAddon.FDSNR3.jointFourierKernel_hasTemperateGrowth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointFourierKernel_hasTemperateGrowth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierParameterBox"
#check @MethbokeAddon.FDSNR3.fourierParameterBox
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierParameterBox"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierParameterBox"
#print axioms MethbokeAddon.FDSNR3.fourierParameterBox
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierParameterBox"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.isOpen_fourierParameterBox"
#check @MethbokeAddon.FDSNR3.isOpen_fourierParameterBox
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.isOpen_fourierParameterBox"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.isOpen_fourierParameterBox"
#print axioms MethbokeAddon.FDSNR3.isOpen_fourierParameterBox
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.isOpen_fourierParameterBox"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_le_of_mem_fourierParameterBox"
#check @MethbokeAddon.FDSNR3.norm_le_of_mem_fourierParameterBox
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_le_of_mem_fourierParameterBox"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_le_of_mem_fourierParameterBox"
#print axioms MethbokeAddon.FDSNR3.norm_le_of_mem_fourierParameterBox
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_le_of_mem_fourierParameterBox"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointFourierIntegrand"
#check @MethbokeAddon.FDSNR3.jointFourierIntegrand
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointFourierIntegrand"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointFourierIntegrand"
#print axioms MethbokeAddon.FDSNR3.jointFourierIntegrand
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointFourierIntegrand"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_jointFourierIntegrand"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_jointFourierIntegrand
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_jointFourierIntegrand"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_jointFourierIntegrand"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_jointFourierIntegrand
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_jointFourierIntegrand"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.norm_fourier_source_jet_le"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.norm_fourier_source_jet_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.norm_fourier_source_jet_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.norm_fourier_source_jet_le"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.norm_fourier_source_jet_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.norm_fourier_source_jet_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.pow_mul_rpow_neg_add"
#check @MethbokeAddon.FDSNR3.pow_mul_rpow_neg_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.pow_mul_rpow_neg_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.pow_mul_rpow_neg_add"
#print axioms MethbokeAddon.FDSNR3.pow_mul_rpow_neg_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.pow_mul_rpow_neg_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.jointFourierIntegrand_jet_bound"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.jointFourierIntegrand_jet_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.jointFourierIntegrand_jet_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.jointFourierIntegrand_jet_bound"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.jointFourierIntegrand_jet_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.jointFourierIntegrand_jet_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity_box"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity_box
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity_box"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity_box"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity_box
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity_box"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.contDiffOn_fourierVelocity"

