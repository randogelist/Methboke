import FDSNR3NonzeroPatch.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure Metric
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate Topology
open LineDeriv
open MethbokeAddon.FDSNR3

noncomputable section

example {g : Vec → ℂ}
    (hg : Continuous g) {x : Vec} (hx : g x ≠ 0) :
    ∃ y : Vec, y ≠ 0 ∧ g y ≠ 0 := by
  apply MethbokeAddon.FDSNR3.continuous_exists_nonzero_point <;> assumption

example {g : Vec → ℂ}
    (hg : Continuous g) {x : Vec} (hx : g x ≠ 0) :
    ∃ ξ₀ : Vec, ∃ r : ℝ,
      ξ₀ ≠ 0 ∧ 0 < r ∧ r < ‖ξ₀‖ ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, g ξ ≠ 0 := by
  apply MethbokeAddon.FDSNR3.continuous_exists_nonzero_ball <;> assumption

example (f : 𝓢(Vec, CVec)) (hf : f ≠ 0) :
    ∃ i : Fin 3, ∃ ξ₀ : Vec, ∃ r : ℝ,
      ξ₀ ≠ 0 ∧ 0 < r ∧ r < ‖ξ₀‖ ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, (𝓕 f ξ) i ≠ 0 := by
  apply MethbokeAddon.FDSNR3.schwartz_exists_nonzero_fourier_ball <;> assumption

example {f : 𝓢(Vec, Vec)} (hf : f ≠ 0) :
    complexifySchwartz f ≠ 0 := by
  apply MethbokeAddon.FDSNR3.complexifySchwartz_ne_zero <;> assumption

example (f : 𝓢(Vec, Vec)) (hf : f ≠ 0) :
    ∃ i : Fin 3, ∃ ξ₀ : Vec, ∃ r : ℝ,
      ξ₀ ≠ 0 ∧ 0 < r ∧ r < ‖ξ₀‖ ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, fourierVelocity f ξ i ≠ 0 := by
  apply MethbokeAddon.FDSNR3.real_schwartz_exists_nonzero_fourier_ball <;> assumption

example {v : Field}
    (f : 𝓢(Vec, Vec)) (hfv : ∀ x : Vec, f x = v x)
    (hv : ∃ x : Vec, v x ≠ 0) :
    ∃ i : Fin 3, ∃ ξ₀ : Vec, ∃ r : ℝ,
      ξ₀ ≠ 0 ∧ 0 < r ∧ r < ‖ξ₀‖ ∧
      ∀ ξ ∈ Metric.ball ξ₀ r, fourierVelocity v ξ i ≠ 0 := by
  apply MethbokeAddon.FDSNR3.physical_exists_nonzero_fourier_ball <;> assumption

example {ξ₀ : Vec} {r : ℝ}
    (hr : r < ‖ξ₀‖) : (0 : Vec) ∉ Metric.closedBall ξ₀ r := by
  apply MethbokeAddon.FDSNR3.zero_notMem_closedBall_of_radius_lt_norm <;> assumption

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.continuous_exists_nonzero_point"
#check @MethbokeAddon.FDSNR3.continuous_exists_nonzero_point
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.continuous_exists_nonzero_point"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.continuous_exists_nonzero_point"
#print axioms MethbokeAddon.FDSNR3.continuous_exists_nonzero_point
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.continuous_exists_nonzero_point"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.continuous_exists_nonzero_ball"
#check @MethbokeAddon.FDSNR3.continuous_exists_nonzero_ball
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.continuous_exists_nonzero_ball"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.continuous_exists_nonzero_ball"
#print axioms MethbokeAddon.FDSNR3.continuous_exists_nonzero_ball
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.continuous_exists_nonzero_ball"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_exists_nonzero_fourier_ball"
#check @MethbokeAddon.FDSNR3.schwartz_exists_nonzero_fourier_ball
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_exists_nonzero_fourier_ball"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_exists_nonzero_fourier_ball"
#print axioms MethbokeAddon.FDSNR3.schwartz_exists_nonzero_fourier_ball
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_exists_nonzero_fourier_ball"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_ne_zero"
#check @MethbokeAddon.FDSNR3.complexifySchwartz_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexifySchwartz_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexifySchwartz_ne_zero"
#print axioms MethbokeAddon.FDSNR3.complexifySchwartz_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexifySchwartz_ne_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.real_schwartz_exists_nonzero_fourier_ball"
#check @MethbokeAddon.FDSNR3.real_schwartz_exists_nonzero_fourier_ball
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.real_schwartz_exists_nonzero_fourier_ball"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.real_schwartz_exists_nonzero_fourier_ball"
#print axioms MethbokeAddon.FDSNR3.real_schwartz_exists_nonzero_fourier_ball
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.real_schwartz_exists_nonzero_fourier_ball"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physical_exists_nonzero_fourier_ball"
#check @MethbokeAddon.FDSNR3.physical_exists_nonzero_fourier_ball
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physical_exists_nonzero_fourier_ball"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physical_exists_nonzero_fourier_ball"
#print axioms MethbokeAddon.FDSNR3.physical_exists_nonzero_fourier_ball
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physical_exists_nonzero_fourier_ball"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.zero_notMem_closedBall_of_radius_lt_norm"
#check @MethbokeAddon.FDSNR3.zero_notMem_closedBall_of_radius_lt_norm
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.zero_notMem_closedBall_of_radius_lt_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.zero_notMem_closedBall_of_radius_lt_norm"
#print axioms MethbokeAddon.FDSNR3.zero_notMem_closedBall_of_radius_lt_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.zero_notMem_closedBall_of_radius_lt_norm"

