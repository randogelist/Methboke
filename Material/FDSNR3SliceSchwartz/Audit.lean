import FDSNR3SliceSchwartz.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set SingularClosure
open scoped BigOperators ContDiff SchwartzMap FourierTransform Topology
open MethbokeAddon.FDSNR3

namespace FDSNR3SliceAudit

noncomputable section

example (x : Vec) :
    spatialSliceCLM x = (0, x) := by
  apply MethbokeAddon.FDSNR3.spatialSliceCLM_apply <;> assumption

example (t : ℝ) (x : Vec) :
    spatialSliceAffine t x = (t, x) := by
  apply MethbokeAddon.FDSNR3.spatialSliceAffine_apply <;> assumption

example (t : ℝ) :
    (spatialSliceAffine t).contLinear = spatialSliceCLM := by
  apply MethbokeAddon.FDSNR3.spatialSliceAffine_contLinear <;> assumption

example {T t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    spatialSliceAffine t ⁻¹' preterminalSpacetime T = (univ : Set Vec) := by
  apply MethbokeAddon.FDSNR3.spatialSliceAffine_preimage <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (ht : t ∈ Ico (0 : ℝ) T) : ContDiff ℝ ∞ (u t) := by
  apply MethbokeAddon.FDSNR3.preterminal_slice_smooth <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (ht : t ∈ Ico (0 : ℝ) T) (n : ℕ) (x : Vec) :
    iteratedFDeriv ℝ n (u t) x =
      (iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x)).compContinuousLinearMap
          (fun _ : Fin n => spatialSliceCLM) := by
  apply MethbokeAddon.FDSNR3.iteratedFDeriv_slice <;> assumption

example {T t : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (ht : t ∈ Ico (0 : ℝ) T) (n : ℕ) (x : Vec) :
    ‖iteratedFDeriv ℝ n (u t) x‖ ≤
      ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x)‖ * ‖spatialSliceCLM‖ ^ n := by
  apply MethbokeAddon.FDSNR3.norm_iteratedFDeriv_slice_le <;> assumption

example {T : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) (x : Vec) :
    hu.slice ht x = u t x := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.slice_apply <;> assumption

example {T : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ f : 𝓢(Vec, Vec), ∀ x : Vec, f x = u t x := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.exists_schwartz_slice <;> assumption

example {T : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) :
    MeasureTheory.Integrable (u t) := by
  apply MethbokeAddon.FDSNR3.LocalSchwartz.slice_integrable <;> assumption

example {ν T : ℝ} {u F : Velocity} {p : Pressure} (hseed : Seed ν T u p F)
    {s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) :
    ∃ t ∈ Ioo s T, ∃ i : Fin 3, ∃ ξ₀ : Vec, ∃ r : ℝ,
      ξ₀ ≠ 0 ∧ 0 < r ∧ r < ‖ξ₀‖ ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, fourierVelocity (u t) ξ i ≠ 0 := by
  apply MethbokeAddon.FDSNR3.Seed.exists_nonzero_fourier_ball_after <;> assumption

-- Literal-definition consumers.
example : spatialSliceCLM =
    (0 : Vec →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ Vec) := rfl

example (t : ℝ) : (spatialSliceAffine t : Vec → ℝ × Vec) = fun x => (t, x) := rfl

example {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {t : ℝ} (ht : t ∈ Ico (0 : ℝ) T) : (hu.slice ht : Vec → Vec) = u t := rfl

end
end FDSNR3SliceAudit

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.spatialSliceCLM"
#check @MethbokeAddon.FDSNR3.spatialSliceCLM
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.spatialSliceCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.spatialSliceCLM"
#print axioms MethbokeAddon.FDSNR3.spatialSliceCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.spatialSliceCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.spatialSliceCLM_apply"
#check @MethbokeAddon.FDSNR3.spatialSliceCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.spatialSliceCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.spatialSliceCLM_apply"
#print axioms MethbokeAddon.FDSNR3.spatialSliceCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.spatialSliceCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.spatialSliceAffine"
#check @MethbokeAddon.FDSNR3.spatialSliceAffine
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.spatialSliceAffine"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.spatialSliceAffine"
#print axioms MethbokeAddon.FDSNR3.spatialSliceAffine
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.spatialSliceAffine"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.spatialSliceAffine_apply"
#check @MethbokeAddon.FDSNR3.spatialSliceAffine_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.spatialSliceAffine_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.spatialSliceAffine_apply"
#print axioms MethbokeAddon.FDSNR3.spatialSliceAffine_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.spatialSliceAffine_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.spatialSliceAffine_contLinear"
#check @MethbokeAddon.FDSNR3.spatialSliceAffine_contLinear
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.spatialSliceAffine_contLinear"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.spatialSliceAffine_contLinear"
#print axioms MethbokeAddon.FDSNR3.spatialSliceAffine_contLinear
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.spatialSliceAffine_contLinear"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.spatialSliceAffine_preimage"
#check @MethbokeAddon.FDSNR3.spatialSliceAffine_preimage
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.spatialSliceAffine_preimage"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.spatialSliceAffine_preimage"
#print axioms MethbokeAddon.FDSNR3.spatialSliceAffine_preimage
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.spatialSliceAffine_preimage"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.preterminal_slice_smooth"
#check @MethbokeAddon.FDSNR3.preterminal_slice_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.preterminal_slice_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.preterminal_slice_smooth"
#print axioms MethbokeAddon.FDSNR3.preterminal_slice_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.preterminal_slice_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.iteratedFDeriv_slice"
#check @MethbokeAddon.FDSNR3.iteratedFDeriv_slice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.iteratedFDeriv_slice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.iteratedFDeriv_slice"
#print axioms MethbokeAddon.FDSNR3.iteratedFDeriv_slice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.iteratedFDeriv_slice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_iteratedFDeriv_slice_le"
#check @MethbokeAddon.FDSNR3.norm_iteratedFDeriv_slice_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_iteratedFDeriv_slice_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_iteratedFDeriv_slice_le"
#print axioms MethbokeAddon.FDSNR3.norm_iteratedFDeriv_slice_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_iteratedFDeriv_slice_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.slice"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.slice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.slice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.slice"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.slice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.slice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.slice_apply"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.slice_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.slice_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.slice_apply"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.slice_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.slice_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.exists_schwartz_slice"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.exists_schwartz_slice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.exists_schwartz_slice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.exists_schwartz_slice"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.exists_schwartz_slice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.exists_schwartz_slice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.slice_integrable"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.slice_integrable
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.slice_integrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.slice_integrable"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.slice_integrable
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.slice_integrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.Seed.exists_nonzero_fourier_ball_after"
#check @MethbokeAddon.FDSNR3.Seed.exists_nonzero_fourier_ball_after
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.Seed.exists_nonzero_fourier_ball_after"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.Seed.exists_nonzero_fourier_ball_after"
#print axioms MethbokeAddon.FDSNR3.Seed.exists_nonzero_fourier_ball_after
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.Seed.exists_nonzero_fourier_ball_after"

