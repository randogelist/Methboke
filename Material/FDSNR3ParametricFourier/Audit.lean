import FDSNR3ParametricFourier.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

section DominatedTaylor

variable {P E A : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace A] {μ : Measure A}

example 
    {F : P → A → E} {p : A → P → FormalMultilinearSeries ℝ P E}
    {s : Set P} (hs : IsOpen s)
    (hTaylor : ∀ a : A, HasFTaylorSeriesUpToOn ∞ (fun q => F q a) (p a) s)
    (hMeas : ∀ n : ℕ, ∀ q ∈ s, AEStronglyMeasurable (fun a => p a q n) μ)
    (hBound : ∀ n : ℕ, ∃ B : A → ℝ, Integrable B μ ∧
      ∀ a : A, ∀ q ∈ s, ‖p a q n‖ ≤ B a) :
    HasFTaylorSeriesUpToOn ∞ (fun q => ∫ a, F q a ∂μ)
      (fun q n => ∫ a, p a q n ∂μ) s := by
  apply MethbokeAddon.FDSNR3.integral_hasFTaylorSeriesUpToOn_of_dominated <;> assumption

example 
    {F : P → A → E} {s : Set P} (hs : IsOpen s)
    (hSmooth : ∀ a : A, ContDiffOn ℝ ∞ (fun q => F q a) s)
    (hMeas : ∀ n : ℕ, ∀ q ∈ s,
      AEStronglyMeasurable
        (fun a => iteratedFDerivWithin ℝ n (fun y => F y a) s q) μ)
    (hBound : ∀ n : ℕ, ∃ B : A → ℝ, Integrable B μ ∧
      ∀ a : A, ∀ q ∈ s,
        ‖iteratedFDerivWithin ℝ n (fun y => F y a) s q‖ ≤ B a) :
    ContDiffOn ℝ ∞ (fun q => ∫ a, F q a ∂μ) s := by
  apply MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_iteratedFDerivWithin <;> assumption

end DominatedTaylor

section JointIntegral

variable (P X : Type*)
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

example : parameterInclusionCLM P X =
    (ContinuousLinearMap.id ℝ P).prod (0 : P →L[ℝ] X) := rfl

example (x : X) : (parameterInclusionAffine P X x : P → P × X) =
    (fun q : P => (q, x)) := rfl

example (x : X) (q : P) :
    parameterInclusionAffine P X x q = (q, x) := by
  apply MethbokeAddon.FDSNR3.parameterInclusionAffine_apply <;> assumption

example (x : X) :
    (parameterInclusionAffine P X x).contLinear = parameterInclusionCLM P X := by
  apply MethbokeAddon.FDSNR3.parameterInclusionAffine_contLinear <;> assumption

example (x : X) (s : Set P) :
    parameterInclusionAffine P X x ⁻¹' (s ×ˢ (univ : Set X)) = s := by
  apply MethbokeAddon.FDSNR3.parameterInclusionAffine_preimage <;> assumption

variable {P X}

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] {μ : Measure X}

example 
    {F : P × X → E} {s : Set P} (hs : IsOpen s)
    (hSmooth : ContDiffOn ℝ ∞ F (s ×ˢ (univ : Set X)))
    (hBound : ∀ n : ℕ, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ q ∈ s, ∀ x : X,
        ‖iteratedFDerivWithin ℝ n F (s ×ˢ univ) (q, x)‖ ≤ B x) :
    ContDiffOn ℝ ∞ (fun q => ∫ x, F (q, x) ∂μ) s := by
  apply MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_joint_jets <;> assumption

end JointIntegral

section FourierContinuity

example {T b : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) (N n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) b, ∀ x : Vec,
      ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x)‖ ≤ C * (1 + ‖x‖) ^ (-(N : ℝ)) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.uniform_jet_decay <;> assumption

example {T b : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) :
    ContinuousOn (fun q : ℝ × Vec => fourierVelocity (u q.1) q.2)
      {q | q.1 ∈ Icc (0 : ℝ) b} := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.continuousOn_fourierVelocity_slab <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) (ξ : Vec) :
    ContinuousAt (fun q : ℝ × Vec => fourierVelocity (u q.1) q.2) (t, ξ) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourierVelocity <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) (ξ : Vec) :
    ContinuousAt (fun r : ℝ => fourierVelocity (u r) ξ) t := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourier_time <;> assumption

end FourierContinuity

section FourierTimeDerivative

example {T t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    preterminalSpacetime T ∈ 𝓝 (t, x) := by
  apply MethbokeAddon.FDSNR3.preterminalSpacetime_mem_nhds <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    HasDerivAt (fun r : ℝ => u r x)
      (fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x) (1, 0)) t := by
  apply MethbokeAddon.FDSNR3.preterminal_hasDerivAt_time_joint <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    timeDerivative u t x =
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x) (1, 0) := by
  apply MethbokeAddon.FDSNR3.preterminal_timeDerivative_eq_joint <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    HasDerivAt (fun r : ℝ => u r x) (timeDerivative u t x) t := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_time <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) :
    Continuous (timeDerivative u t) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.continuous_timeDerivative_slice <;> assumption

example {T b : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0 : ℝ) b, ∀ x : Vec,
      ‖timeDerivative u t x‖ ≤ C * (1 + ‖x‖) ^ (-(N : ℝ)) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.uniform_timeDerivative_decay <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) :
    Integrable (timeDerivative u t) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_integrable <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) (ξ : Vec) :
    HasDerivAt (fun r : ℝ => fourierVelocity (u r) ξ)
      (fourierVelocity (timeDerivative u t) ξ) t := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_fourier_time <;> assumption

end FourierTimeDerivative

end

end MethbokeAddon.FDSNR3

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.integral_hasFTaylorSeriesUpToOn_of_dominated"
#check @MethbokeAddon.FDSNR3.integral_hasFTaylorSeriesUpToOn_of_dominated
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.integral_hasFTaylorSeriesUpToOn_of_dominated"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.integral_hasFTaylorSeriesUpToOn_of_dominated"
#print axioms MethbokeAddon.FDSNR3.integral_hasFTaylorSeriesUpToOn_of_dominated
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.integral_hasFTaylorSeriesUpToOn_of_dominated"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_iteratedFDerivWithin"
#check @MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_iteratedFDerivWithin
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_iteratedFDerivWithin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_iteratedFDerivWithin"
#print axioms MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_iteratedFDerivWithin
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_iteratedFDerivWithin"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.parameterInclusionCLM"
#check @MethbokeAddon.FDSNR3.parameterInclusionCLM
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.parameterInclusionCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.parameterInclusionCLM"
#print axioms MethbokeAddon.FDSNR3.parameterInclusionCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.parameterInclusionCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.parameterInclusionAffine"
#check @MethbokeAddon.FDSNR3.parameterInclusionAffine
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.parameterInclusionAffine"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.parameterInclusionAffine"
#print axioms MethbokeAddon.FDSNR3.parameterInclusionAffine
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.parameterInclusionAffine"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.parameterInclusionAffine_apply"
#check @MethbokeAddon.FDSNR3.parameterInclusionAffine_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.parameterInclusionAffine_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.parameterInclusionAffine_apply"
#print axioms MethbokeAddon.FDSNR3.parameterInclusionAffine_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.parameterInclusionAffine_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.parameterInclusionAffine_contLinear"
#check @MethbokeAddon.FDSNR3.parameterInclusionAffine_contLinear
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.parameterInclusionAffine_contLinear"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.parameterInclusionAffine_contLinear"
#print axioms MethbokeAddon.FDSNR3.parameterInclusionAffine_contLinear
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.parameterInclusionAffine_contLinear"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.parameterInclusionAffine_preimage"
#check @MethbokeAddon.FDSNR3.parameterInclusionAffine_preimage
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.parameterInclusionAffine_preimage"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.parameterInclusionAffine_preimage"
#print axioms MethbokeAddon.FDSNR3.parameterInclusionAffine_preimage
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.parameterInclusionAffine_preimage"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_joint_jets"
#check @MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_joint_jets
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_joint_jets"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_joint_jets"
#print axioms MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_joint_jets
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.contDiffOn_integral_of_dominated_joint_jets"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.uniform_jet_decay"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.uniform_jet_decay
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.uniform_jet_decay"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.uniform_jet_decay"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.uniform_jet_decay
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.uniform_jet_decay"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.continuousOn_fourierVelocity_slab"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.continuousOn_fourierVelocity_slab
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.continuousOn_fourierVelocity_slab"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.continuousOn_fourierVelocity_slab"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.continuousOn_fourierVelocity_slab
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.continuousOn_fourierVelocity_slab"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourierVelocity"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourierVelocity
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourierVelocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourierVelocity"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourierVelocity
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourierVelocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourier_time"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourier_time
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourier_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourier_time"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourier_time
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.continuousAt_fourier_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.preterminalSpacetime_mem_nhds"
#check @MethbokeAddon.FDSNR3.preterminalSpacetime_mem_nhds
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.preterminalSpacetime_mem_nhds"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.preterminalSpacetime_mem_nhds"
#print axioms MethbokeAddon.FDSNR3.preterminalSpacetime_mem_nhds
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.preterminalSpacetime_mem_nhds"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.preterminal_hasDerivAt_time_joint"
#check @MethbokeAddon.FDSNR3.preterminal_hasDerivAt_time_joint
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.preterminal_hasDerivAt_time_joint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.preterminal_hasDerivAt_time_joint"
#print axioms MethbokeAddon.FDSNR3.preterminal_hasDerivAt_time_joint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.preterminal_hasDerivAt_time_joint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.preterminal_timeDerivative_eq_joint"
#check @MethbokeAddon.FDSNR3.preterminal_timeDerivative_eq_joint
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.preterminal_timeDerivative_eq_joint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.preterminal_timeDerivative_eq_joint"
#print axioms MethbokeAddon.FDSNR3.preterminal_timeDerivative_eq_joint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.preterminal_timeDerivative_eq_joint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_time"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_time
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_time"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_time
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.continuous_timeDerivative_slice"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.continuous_timeDerivative_slice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.continuous_timeDerivative_slice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.continuous_timeDerivative_slice"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.continuous_timeDerivative_slice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.continuous_timeDerivative_slice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.uniform_timeDerivative_decay"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.uniform_timeDerivative_decay
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.uniform_timeDerivative_decay"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.uniform_timeDerivative_decay"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.uniform_timeDerivative_decay
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.uniform_timeDerivative_decay"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_integrable"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_integrable
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_integrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_integrable"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_integrable
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_integrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_fourier_time"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_fourier_time
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_fourier_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_fourier_time"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_fourier_time
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_fourier_time"

