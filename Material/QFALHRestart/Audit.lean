import QFALHRestart.Endpoint

set_option autoImplicit false
set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Interval Topology
open MethbokeAddon.QuasiFeffermanA
open QFA.Representation

namespace QFALHRestart.IndependentTypeChecks

-- Independent literal test consumer: no replacement notion of weak test.
example (φ : MomentumTest) (s : ℝ) (hs : 0 ≤ s) :
    MomentumTest := MomentumTest.restart φ s hs

example (φ : MomentumTest) (s : ℝ) (hs : 0 ≤ s) (z : ℝ × Space) :
    (MomentumTest.restart φ s hs).value z = φ.value (z.1 - s, z.2) := rfl

example (φ : MomentumTest) (s : ℝ) (hs : 0 ≤ s) (t : ℝ) (x : Space) :
    (MomentumTest.restart φ s hs).value (t, x) = φ.value (t - s, x) :=
  MomentumTest.restart_value φ s hs t x

example (φ : MomentumTest) (s : ℝ) (hs : 0 ≤ s) (t : ℝ) (x : Space) :
    fderiv ℝ (fun r : ℝ => (MomentumTest.restart φ s hs).value (r, x)) t =
      fderiv ℝ (fun r : ℝ => φ.value (r, x)) (t - s) :=
  MomentumTest.restart_time_fderiv φ s hs t x

example (φ : MomentumTest) (s : ℝ) (hs : 0 ≤ s) (t : ℝ) (x : Space) :
    fderiv ℝ (fun y : Space => (MomentumTest.restart φ s hs).value (t, y)) x =
      fderiv ℝ (fun y : Space => φ.value (t - s, y)) x :=
  MomentumTest.restart_spatial_fderiv φ s hs t x

example (s : ℝ) (hs : 0 ≤ s) (u : Velocity) (φ : MomentumTest)
    (t : ℝ) (x : Space) :
    inner ℝ (u (t + s) x) (fderiv ℝ (fun r : ℝ => φ.value (r, x)) t 1) =
      inner ℝ (u (t + s) x)
        (fderiv ℝ (fun r : ℝ => (MomentumTest.restart φ s hs).value (r, x))
          (t + s) 1) :=
  momentumTimeIntegrand_timeTranslate s hs u φ t x

example (s : ℝ) (hs : 0 ≤ s) (u : Velocity) (φ : MomentumTest)
    (t : ℝ) (x : Space) :
    (∑ j : Fin 3, (u (t + s) x) j * inner ℝ (u (t + s) x)
      (fderiv ℝ (fun y : Space => φ.value (t, y)) x (coordinateVector j))) =
      ∑ j : Fin 3, (u (t + s) x) j * inner ℝ (u (t + s) x)
        (fderiv ℝ (fun y : Space => (MomentumTest.restart φ s hs).value (t + s, y))
          x (coordinateVector j)) :=
  momentumConvectionIntegrand_timeTranslate s hs u φ t x

example (s : ℝ) (hs : 0 ≤ s) (G : WeakGradient) (φ : MomentumTest)
    (t : ℝ) (x : Space) :
    (∑ j : Fin 3, inner ℝ (G (t + s) j x)
      (fderiv ℝ (fun y : Space => φ.value (t, y)) x (coordinateVector j))) =
      ∑ j : Fin 3, inner ℝ (G (t + s) j x)
        (fderiv ℝ (fun y : Space => (MomentumTest.restart φ s hs).value (t + s, y))
          x (coordinateVector j)) :=
  momentumDissipationIntegrand_timeTranslate s hs G φ t x

example (s : ℝ) :
    MeasurePreserving (fun t : ℝ => t + s)
      (volume.restrict (Ioi (0 : ℝ))) (volume.restrict (Ioi s)) :=
  timeTranslate_measurePreserving_Ioi s

example {s : ℝ} (hs : 0 ≤ s) {f : ℝ → ℝ}
    (hf : Integrable f (volume.restrict (Ioi (0 : ℝ)))) :
    Integrable (fun t : ℝ => f (t + s)) (volume.restrict (Ioi (0 : ℝ))) :=
  timeTranslate_integrable_Ioi hs hf

example {s : ℝ} (hs : 0 ≤ s) (f : ℝ → ℝ)
    (hzero : ∀ t : ℝ, t ≤ s → f t = 0) :
    (∫ t in Ioi (0 : ℝ), f (t + s)) = ∫ t in Ioi (0 : ℝ), f t :=
  timeTranslate_integral_Ioi_of_zero_before hs f hzero

-- Original concrete WeakMomentum, with no PDE-translation port among the premises.
example {ν s : ℝ} {u : Velocity} {G : WeakGradient}
    (h : WeakMomentum ν u G) (hs : 0 ≤ s) :
    WeakMomentum ν (fun t => u (t + s)) (fun t => G (t + s)) :=
  WeakMomentum.timeTranslate h hs

example {P : ℝ → Prop} {s R : ℝ} (hs : 0 ≤ s)
    (hP : ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) (R + s)), P t) :
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), P (t + s) :=
  MethbokeAddon.QuasiFeffermanA.timeTranslate_ae_Ioo hs hP

-- Literal energy inequalities at every upper endpoint, with actual L2 norms.
example {ν s r : ℝ} {u : Velocity} {G : WeakGradient}
    (hstart : ∀ t : ℝ, r + s ≤ t →
      ‖u t‖ ^ 2 + 2 * ν * (∫ q in (r + s)..t, ∑ j : Fin 3, ‖G q j‖ ^ 2) ≤
        ‖u (r + s)‖ ^ 2) :
    ∀ t : ℝ, r ≤ t →
      ‖u (t + s)‖ ^ 2 + 2 * ν *
        (∫ q in r..t, ∑ j : Fin 3, ‖G (q + s) j‖ ^ 2) ≤ ‖u (r + s)‖ ^ 2 :=
  energyStart_timeTranslate hstart

-- No viscosity sign, strong trace, restart membership, existence, or comparison
-- premise is introduced into this exact supplied-path membership theorem.
example {ν s : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hs : 0 ≤ s)
    (hstart : ∀ t : ℝ, s ≤ t →
      ‖u t‖ ^ 2 + 2 * ν * (∫ q in s..t, ∑ j : Fin 3, ‖G q j‖ ^ 2) ≤ ‖u s‖ ^ 2) :
    LerayHopf ν (u s) (fun t => u (t + s)) (fun t => G (t + s)) :=
  LerayHopf.timeTranslate h hs hstart

example {ν R : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hR : 0 < R) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R),
      Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
        EnergyStart ν u G s ∧
        LerayHopf ν (u s) (fun t => u (t + s)) (fun t => G (t + s)) :=
  LerayHopf.ae_full_restart h hR

example {ν R : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hν : 0 ≤ ν) (hR : 0 < R) :
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R),
      GoodRestart ν u G s ∧
        LerayHopf ν (u s) (fun t => u (t + s)) (fun t => G (t + s)) :=
  LerayHopf.goodRestart_and_full_restart_ae h hν hR

example {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hS : 0 < S) (hν : 0 < ν) (ha : a ≠ 0) :
    (safeCutoff S ‖a‖ ν / 2 ≤
      (volume.restrict (Ioo (0 : ℝ) (safeCutoff S ‖a‖ ν))).real
        {s | (GoodRestart ν u G s ∧
          LerayHopf ν (u s) (fun t => u (t + s)) (fun t => G (t + s))) ∧
          ‖u s‖ ^ 2 * (∑ j : Fin 3, ‖G s j‖ ^ 2) < ν ^ 4 / S ^ 6}) ∧
      ∃ s, 0 < s ∧ s < safeCutoff S ‖a‖ ν ∧
        (GoodRestart ν u G s ∧
          LerayHopf ν (u s) (fun t => u (t + s)) (fun t => G (t + s))) ∧
        ‖u s‖ ^ 2 * (∑ j : Fin 3, ‖G s j‖ ^ 2) < ν ^ 4 / S ^ 6 :=
  LerayHopf.safe_window_full_restart_and_measure h hS hν ha

example {S ν : ℝ} {a : SpatialL2} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν a u G) (hS : 0 < S) (hν : 0 < ν) (ha : a ≠ 0) :
    ∃ s, 0 < s ∧ s < S ^ 6 * ‖a‖ ^ 4 / (2 * ν ^ 5) ∧
      Solenoidal (u s) ∧ SpatialWeakGradient (u s) (G s) ∧
      EnergyStart ν u G s ∧ QFA.Assembly.Restart.RestartData ν u G s ∧
      LerayHopf ν (u s) (fun t => u (t + s)) (fun t => G (t + s)) ∧
      Tendsto u (𝓝[>] s) (𝓝 (u s)) ∧
      ‖u s‖ ^ 2 * (∑ j : Fin 3, ‖G s j‖ ^ 2) < ν ^ 4 / S ^ 6 :=
  LerayHopf.exists_safe_full_restart h hS hν ha

end QFALHRestart.IndependentTypeChecks

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart"
#check @MethbokeAddon.QuasiFeffermanA.MomentumTest.restart
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart"
#print axioms MethbokeAddon.QuasiFeffermanA.MomentumTest.restart
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_value"
#check @MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_value
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_value"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_value"
#print axioms MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_value
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_value"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_time_fderiv"
#check @MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_time_fderiv
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_time_fderiv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_time_fderiv"
#print axioms MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_time_fderiv
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_time_fderiv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_spatial_fderiv"
#check @MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_spatial_fderiv
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_spatial_fderiv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_spatial_fderiv"
#print axioms MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_spatial_fderiv
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.MomentumTest.restart_spatial_fderiv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand_timeTranslate"
#check @MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand_timeTranslate
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand_timeTranslate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand_timeTranslate"
#print axioms MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand_timeTranslate
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.momentumTimeIntegrand_timeTranslate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand_timeTranslate"
#check @MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand_timeTranslate
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand_timeTranslate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand_timeTranslate"
#print axioms MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand_timeTranslate
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.momentumConvectionIntegrand_timeTranslate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand_timeTranslate"
#check @MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand_timeTranslate
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand_timeTranslate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand_timeTranslate"
#print axioms MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand_timeTranslate
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.momentumDissipationIntegrand_timeTranslate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.timeTranslate_measurePreserving_Ioi"
#check @MethbokeAddon.QuasiFeffermanA.timeTranslate_measurePreserving_Ioi
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.timeTranslate_measurePreserving_Ioi"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.timeTranslate_measurePreserving_Ioi"
#print axioms MethbokeAddon.QuasiFeffermanA.timeTranslate_measurePreserving_Ioi
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.timeTranslate_measurePreserving_Ioi"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.timeTranslate_integrable_Ioi"
#check @MethbokeAddon.QuasiFeffermanA.timeTranslate_integrable_Ioi
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.timeTranslate_integrable_Ioi"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.timeTranslate_integrable_Ioi"
#print axioms MethbokeAddon.QuasiFeffermanA.timeTranslate_integrable_Ioi
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.timeTranslate_integrable_Ioi"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.timeTranslate_integral_Ioi_of_zero_before"
#check @MethbokeAddon.QuasiFeffermanA.timeTranslate_integral_Ioi_of_zero_before
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.timeTranslate_integral_Ioi_of_zero_before"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.timeTranslate_integral_Ioi_of_zero_before"
#print axioms MethbokeAddon.QuasiFeffermanA.timeTranslate_integral_Ioi_of_zero_before
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.timeTranslate_integral_Ioi_of_zero_before"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.WeakMomentum.timeTranslate"
#check @MethbokeAddon.QuasiFeffermanA.WeakMomentum.timeTranslate
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.WeakMomentum.timeTranslate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.WeakMomentum.timeTranslate"
#print axioms MethbokeAddon.QuasiFeffermanA.WeakMomentum.timeTranslate
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.WeakMomentum.timeTranslate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.timeTranslate_ae_Ioo"
#check @MethbokeAddon.QuasiFeffermanA.timeTranslate_ae_Ioo
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.timeTranslate_ae_Ioo"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.timeTranslate_ae_Ioo"
#print axioms MethbokeAddon.QuasiFeffermanA.timeTranslate_ae_Ioo
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.timeTranslate_ae_Ioo"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.energyStart_timeTranslate"
#check @MethbokeAddon.QuasiFeffermanA.energyStart_timeTranslate
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.energyStart_timeTranslate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.energyStart_timeTranslate"
#print axioms MethbokeAddon.QuasiFeffermanA.energyStart_timeTranslate
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.energyStart_timeTranslate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.timeTranslate"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.timeTranslate
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.timeTranslate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.timeTranslate"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.timeTranslate
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.timeTranslate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_full_restart"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_full_restart
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_full_restart"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_full_restart"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_full_restart
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.ae_full_restart"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_and_full_restart_ae"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_and_full_restart_ae
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_and_full_restart_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_and_full_restart_ae"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_and_full_restart_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.goodRestart_and_full_restart_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_full_restart_and_measure"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_full_restart_and_measure
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_full_restart_and_measure"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_full_restart_and_measure"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_full_restart_and_measure
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.safe_window_full_restart_and_measure"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_full_restart"
#check @MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_full_restart
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_full_restart"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_full_restart"
#print axioms MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_full_restart
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.LerayHopf.exists_safe_full_restart"
