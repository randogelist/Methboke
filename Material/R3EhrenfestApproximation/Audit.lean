import R3EhrenfestApproximation.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators FourierTransform Topology UniformConvergence

namespace R3EhrenfestApproximation.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers
open MethbokeAddon.R3Ehrenfest.SharpCutoff
open MethbokeAddon.R3Ehrenfest.Approximation
open QFA.Endpoints.Agmon (ComplexL2)

example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

-- The limiting mask is the literal n+1 closed-ball indicator.
example (ξ : Space) :
    ∀ᶠ n : ℕ in atTop, (if ‖ξ‖ ≤ (n : ℝ) + 1 then (1 : ℝ) else 0) = 1 :=
  cutoffValue_eventually_one ξ

-- Strong convergence is concluded for every native L2 input, with no density or convergence premise.
example (f : ComplexL2) :
    Tendsto (fun n : ℕ => frequencyMultiplier (cutoffSymbol n) f) atTop (𝓝 f) :=
  tendsto_frequencyMultiplier_cutoff f
example (u : SpatialL2) :
    Tendsto (fun n : ℕ => sharpCutoff n u) atTop (𝓝 u) := tendsto_sharpCutoff u
example (u : SpatialL2) :
    Tendsto (fun n : ℕ => ‖sharpCutoff n u - u‖) atTop (𝓝 (0 : ℝ)) :=
  norm_sharpCutoff_sub_tendsto_zero u

-- The same convergence holds in the existing physical H1 graph norm.
example (u : PhysicalH1) :
    Tendsto (fun n : ℕ => physicalH1SharpCutoff n u) atTop (𝓝 u) :=
  tendsto_physicalH1SharpCutoff u
example (u : PhysicalH1) :
    Tendsto (fun n : ℕ => physicalH1SharpCutoffCLM n u) atTop (𝓝 u) :=
  tendsto_physicalH1SharpCutoffCLM u
example (u : PhysicalH1) :
    Tendsto (fun n : ℕ => ‖physicalH1SharpCutoff n u - u‖) atTop (𝓝 (0 : ℝ)) :=
  norm_physicalH1SharpCutoff_sub_tendsto_zero u
example (n : ℕ) (u v : PhysicalH1) :
    dist (physicalH1SharpCutoff n u) (physicalH1SharpCutoff n v) ≤ dist u v :=
  dist_physicalH1SharpCutoff_le n u v

-- Compactness belongs to the supplied set or continuous trajectory image.
example (K : Set PhysicalH1) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n : ℕ => physicalH1SharpCutoff n) (fun u => u) atTop K :=
  tendstoUniformlyOn_physicalH1SharpCutoff K hK
example (U : ℝ → PhysicalH1) (T : ℝ) (hU : ContinuousOn U (Icc 0 T)) :
    TendstoUniformlyOn (fun n : ℕ => fun t : ℝ => physicalH1SharpCutoff n (U t))
      U atTop (Icc 0 T) :=
  tendstoUniformlyOn_physicalH1SharpCutoff_trajectory U T hU

end R3EhrenfestApproximation.ExpectedTypes

-- Ordered exact-type and named axiom reports; external authorized execution only.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.cutoffValue_eventually_one"
#check @MethbokeAddon.R3Ehrenfest.Approximation.cutoffValue_eventually_one
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Approximation.cutoffValue_eventually_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.cutoffValue_eventually_one"
#print axioms MethbokeAddon.R3Ehrenfest.Approximation.cutoffValue_eventually_one
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Approximation.cutoffValue_eventually_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_frequencyMultiplier_cutoff"
#check @MethbokeAddon.R3Ehrenfest.Approximation.tendsto_frequencyMultiplier_cutoff
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_frequencyMultiplier_cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_frequencyMultiplier_cutoff"
#print axioms MethbokeAddon.R3Ehrenfest.Approximation.tendsto_frequencyMultiplier_cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_frequencyMultiplier_cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_sharpCutoff"
#check @MethbokeAddon.R3Ehrenfest.Approximation.tendsto_sharpCutoff
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_sharpCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_sharpCutoff"
#print axioms MethbokeAddon.R3Ehrenfest.Approximation.tendsto_sharpCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_sharpCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.norm_sharpCutoff_sub_tendsto_zero"
#check @MethbokeAddon.R3Ehrenfest.Approximation.norm_sharpCutoff_sub_tendsto_zero
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Approximation.norm_sharpCutoff_sub_tendsto_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.norm_sharpCutoff_sub_tendsto_zero"
#print axioms MethbokeAddon.R3Ehrenfest.Approximation.norm_sharpCutoff_sub_tendsto_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Approximation.norm_sharpCutoff_sub_tendsto_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoff"
#check @MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoff
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoff"
#print axioms MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoffCLM"
#check @MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoffCLM
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoffCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoffCLM"
#print axioms MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoffCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Approximation.tendsto_physicalH1SharpCutoffCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.norm_physicalH1SharpCutoff_sub_tendsto_zero"
#check @MethbokeAddon.R3Ehrenfest.Approximation.norm_physicalH1SharpCutoff_sub_tendsto_zero
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Approximation.norm_physicalH1SharpCutoff_sub_tendsto_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.norm_physicalH1SharpCutoff_sub_tendsto_zero"
#print axioms MethbokeAddon.R3Ehrenfest.Approximation.norm_physicalH1SharpCutoff_sub_tendsto_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Approximation.norm_physicalH1SharpCutoff_sub_tendsto_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.dist_physicalH1SharpCutoff_le"
#check @MethbokeAddon.R3Ehrenfest.Approximation.dist_physicalH1SharpCutoff_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Approximation.dist_physicalH1SharpCutoff_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.dist_physicalH1SharpCutoff_le"
#print axioms MethbokeAddon.R3Ehrenfest.Approximation.dist_physicalH1SharpCutoff_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Approximation.dist_physicalH1SharpCutoff_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff"
#check @MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff"
#print axioms MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff_trajectory"
#check @MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff_trajectory
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff_trajectory"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff_trajectory"
#print axioms MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff_trajectory
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Approximation.tendstoUniformlyOn_physicalH1SharpCutoff_trajectory"

