import FDSNR3SchwartzJets.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ContDiff SchwartzMap Topology
open LineDeriv

noncomputable section

section General
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

example : (familySpatialInclusion : E →L[ℝ] (ℝ × E)) =
    (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E) := rfl

example (G : 𝓢(ℝ × E, F)) : schwartzSliceJet G 0 =
    SchwartzMap.postcompCLM
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearMap G := rfl

example (G : 𝓢(ℝ × E, F)) (n : ℕ) : schwartzSliceJet G (n+1) =
    SchwartzMap.postcompCLM
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F)
        .symm.toContinuousLinearMap
      (SchwartzMap.postcompCLM
        ((ContinuousLinearMap.compL ℝ E (ℝ × E)
          (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)).flip familySpatialInclusion)
        (SchwartzMap.fderivCLM ℝ (ℝ × E)
          (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) (schwartzSliceJet G n))) := rfl

example (z : E) :
    familySpatialInclusion z = ((0 : ℝ), z) := by
  apply MethbokeAddon.FDSNR3.familySpatialInclusion_apply <;> assumption

example (G : 𝓢(ℝ × E, F)) (n : ℕ) (q : ℝ × E) :
    schwartzSliceJet G n q =
      iteratedFDeriv ℝ n (fun z : E => G (q.1, z)) q.2 := by
  apply MethbokeAddon.FDSNR3.schwartzSliceJet_apply <;> assumption

example (G : 𝓢(ℝ × E, F)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, ∀ z : E,
      (1 + ‖z‖) ^ N * ‖G (lam, z)‖ ≤ C := by
  apply MethbokeAddon.FDSNR3.schwartz_weighted_value_bound <;> assumption

example (G : 𝓢(ℝ × E, F)) (hzero : ∀ z : E, G (0, z) = 0) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, ∀ z : E,
      (1 + ‖z‖) ^ N * ‖G (lam, z)‖ ≤ C * |lam| := by
  apply MethbokeAddon.FDSNR3.schwartz_weighted_value_linear_bound <;> assumption

example (G : 𝓢(ℝ × E, F)) (hzero : ∀ z : E, G (0, z) = 0) (N n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, ∀ z : E,
      (1 + ‖z‖) ^ N *
        ‖iteratedFDeriv ℝ n (fun y : E => G (lam, y)) z‖ ≤ C * |lam| := by
  apply MethbokeAddon.FDSNR3.schwartz_weighted_sliceJet_linear_bound <;> assumption

example (G : 𝓢(ℝ × E, F)) (hzero : ∀ z : E, G (0, z) = 0) (N r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, ∀ n : ℕ, n ≤ r → ∀ z : E,
      (1 + ‖z‖) ^ N *
        ‖iteratedFDeriv ℝ n (fun y : E => G (lam, y)) z‖ ≤ C * |lam| := by
  apply MethbokeAddon.FDSNR3.schwartz_weighted_finite_sliceJet_linear_bound <;> assumption

end General

example (ε : ℝ) (u F : Velocity) (U G : ℝ → Velocity)
    (H J : 𝓢(ℝ × (ℝ × Vec), Vec))
    (hH : ∀ lam : ℝ, ∀ z : ℝ × Vec, H (lam, z) = (U lam - u) z.1 z.2)
    (hJ : ∀ lam : ℝ, ∀ z : ℝ × Vec, J (lam, z) = (G lam - F) z.1 z.2)
    (hH0 : ∀ z : ℝ × Vec, H (0, z) = 0)
    (hJ0 : ∀ z : ℝ × Vec, J (0, z) = 0) :
    WeightedSmoothSmallness ε u F U G := by
  apply MethbokeAddon.FDSNR3.weightedSmoothSmallness_of_schwartz_corrections <;> assumption

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familySpatialInclusion"
#check @MethbokeAddon.FDSNR3.familySpatialInclusion
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familySpatialInclusion"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familySpatialInclusion"
#print axioms MethbokeAddon.FDSNR3.familySpatialInclusion
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familySpatialInclusion"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.familySpatialInclusion_apply"
#check @MethbokeAddon.FDSNR3.familySpatialInclusion_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.familySpatialInclusion_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.familySpatialInclusion_apply"
#print axioms MethbokeAddon.FDSNR3.familySpatialInclusion_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.familySpatialInclusion_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzSliceJet"
#check @MethbokeAddon.FDSNR3.schwartzSliceJet
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzSliceJet"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzSliceJet"
#print axioms MethbokeAddon.FDSNR3.schwartzSliceJet
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzSliceJet"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartzSliceJet_apply"
#check @MethbokeAddon.FDSNR3.schwartzSliceJet_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartzSliceJet_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartzSliceJet_apply"
#print axioms MethbokeAddon.FDSNR3.schwartzSliceJet_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartzSliceJet_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_weighted_value_bound"
#check @MethbokeAddon.FDSNR3.schwartz_weighted_value_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_weighted_value_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_weighted_value_bound"
#print axioms MethbokeAddon.FDSNR3.schwartz_weighted_value_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_weighted_value_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_weighted_value_linear_bound"
#check @MethbokeAddon.FDSNR3.schwartz_weighted_value_linear_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_weighted_value_linear_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_weighted_value_linear_bound"
#print axioms MethbokeAddon.FDSNR3.schwartz_weighted_value_linear_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_weighted_value_linear_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_weighted_sliceJet_linear_bound"
#check @MethbokeAddon.FDSNR3.schwartz_weighted_sliceJet_linear_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_weighted_sliceJet_linear_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_weighted_sliceJet_linear_bound"
#print axioms MethbokeAddon.FDSNR3.schwartz_weighted_sliceJet_linear_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_weighted_sliceJet_linear_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.schwartz_weighted_finite_sliceJet_linear_bound"
#check @MethbokeAddon.FDSNR3.schwartz_weighted_finite_sliceJet_linear_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.schwartz_weighted_finite_sliceJet_linear_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.schwartz_weighted_finite_sliceJet_linear_bound"
#print axioms MethbokeAddon.FDSNR3.schwartz_weighted_finite_sliceJet_linear_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.schwartz_weighted_finite_sliceJet_linear_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.weightedSmoothSmallness_of_schwartz_corrections"
#check @MethbokeAddon.FDSNR3.weightedSmoothSmallness_of_schwartz_corrections
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.weightedSmoothSmallness_of_schwartz_corrections"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.weightedSmoothSmallness_of_schwartz_corrections"
#print axioms MethbokeAddon.FDSNR3.weightedSmoothSmallness_of_schwartz_corrections
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.weightedSmoothSmallness_of_schwartz_corrections"

