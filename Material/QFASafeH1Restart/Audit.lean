import QFASafeH1Restart.Endpoint

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators Interval Topology
open MethbokeAddon.QuasiFeffermanA
open QFA.Representation QFA.Endpoints.Restart

namespace QFASafeH1Restart.IndependentTypeChecks

example (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (hgrad : SpatialWeakGradient v G) (hsol : Solenoidal v) :
    PhysicalH1Sigma :=
  physicalH1SigmaOfWeakGradient v G hgrad hsol

example (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (hgrad : SpatialWeakGradient v G) (hsol : Solenoidal v) :
    (physicalH1SigmaOfWeakGradient v G hgrad hsol).val 0 = v :=
  physicalH1SigmaOfWeakGradient_velocity v G hgrad hsol

example (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (hgrad : SpatialWeakGradient v G) (hsol : Solenoidal v) (j : Fin 3) :
    (physicalH1SigmaOfWeakGradient v G hgrad hsol).val j.succ = G j :=
  physicalH1SigmaOfWeakGradient_gradient v G hgrad hsol j

-- Literal field consumer: all data belong to one time and the same original path.
example {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (r : SafeH1Restart S ν a u G) :
    0 < r.time ∧
      r.time < safeCutoff S ‖a‖ ν ∧
      r.datum.val 0 = u r.time ∧
      (∀ j : Fin 3, r.datum.val j.succ = G r.time j) ∧
      EnergyStart ν u G r.time ∧
      QFA.Assembly.Restart.RestartData ν u G r.time ∧
      LerayHopf ν (u r.time)
        (fun t => u (t + r.time))
        (fun t => G (t + r.time)) ∧
      Tendsto u (𝓝[>] r.time) (𝓝 (u r.time)) ∧
      velocityEnergy (u r.time) * gradientEnergy (G r.time) < productThreshold S ν :=
  ⟨r.time_pos, r.time_lt_cutoff, r.datum_velocity, r.datum_gradient,
    r.energy_start, r.restart_data, r.shifted_leray_hopf,
    r.right_trace, r.small_product⟩

example {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (r : SafeH1Restart S ν a u G) :
    ‖r.datum‖ ^ 2 = ‖u r.time‖ ^ 2 + ∑ j : Fin 3, ‖G r.time j‖ ^ 2 := by
  simpa only [velocityEnergy, gradientEnergy] using r.datum_norm_sq

example {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (r : SafeH1Restart S ν a u G) :
    velocityEnergy (r.datum.val 0) *
        gradientEnergy (fun j : Fin 3 => r.datum.val j.succ) <
      productThreshold S ν :=
  r.datum_small_product

-- No existence, comparison, continuation or smoothness premise is added.
example {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hS : 0 < S) (hν : 0 < ν) (ha : a ≠ 0) :
    Nonempty (SafeH1Restart S ν a u G) :=
  LerayHopf.exists_safe_h1_restart h hS hν ha

end QFASafeH1Restart.IndependentTypeChecks

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_velocity"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_gradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaOfWeakGradient_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SafeH1Restart"
#check @MethbokeAddon.QuasiFeffermanA.SafeH1Restart
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SafeH1Restart"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SafeH1Restart"
#print axioms MethbokeAddon.QuasiFeffermanA.SafeH1Restart
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SafeH1Restart"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_norm_sq"
#check @MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_norm_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_small_product"
#check @MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_small_product
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_small_product"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_small_product"
#print axioms MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_small_product
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SafeH1Restart.datum_small_product"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_h1_restart"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_h1_restart
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_h1_restart"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_h1_restart"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_h1_restart
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_h1_restart"
