import WFBMaximalLerayHopfIdentification.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped ENNReal
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_front_leray_hopf_identification
example : ∀ (ν : ℝ) (a : Field) (u v : Velocity) (p : Pressure)
    (G : WeakGradientTrajectory) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (ha : SmoothSigmaZero a)
    (H : MaximalClassicalFront ν a u p Tmax)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G),
    ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax →
      v t =ᵐ[volume.restrict unitCube] u t :=
  @MethbokeAddon.WeakFouriermanB.maximal_front_leray_hopf_identification

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_front_original_leray_hopf
example : ∀ (ν : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (ha : SmoothSigmaZero a)
    (H : MaximalClassicalFront ν a u p Tmax),
    ∃ (v : Velocity) (G : WeakGradientTrajectory),
      CriticalLerayHopf ν (criticalL2Representative a) v G ∧
      (v 0 =ᵐ[volume.restrict unitCube] a) ∧
      ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax →
        v t =ᵐ[volume.restrict unitCube] u t :=
  @MethbokeAddon.WeakFouriermanB.maximal_front_original_leray_hopf

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_leray_hopf_identification"
#check @MethbokeAddon.WeakFouriermanB.maximal_front_leray_hopf_identification
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_front_leray_hopf_identification"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_leray_hopf_identification"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_front_leray_hopf_identification
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_front_leray_hopf_identification"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_original_leray_hopf"
#check @MethbokeAddon.WeakFouriermanB.maximal_front_original_leray_hopf
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_front_original_leray_hopf"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_original_leray_hopf"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_front_original_leray_hopf
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_front_original_leray_hopf"
