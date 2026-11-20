import WFBMaximalTailGluing.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory SingularClosure QuasiFeffermanB
open scoped ENNReal
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_front_tail_overlap_of_same_leray_hopf
example : ∀ (ν δ : ℝ) (a : Field) (u v w : Velocity) (p q : Pressure)
    (G : WeakGradientTrajectory) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (ha : SmoothSigmaZero a)
    (H : MaximalClassicalFront ν a u p Tmax)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (K : ClassicalTail ν δ w q) (hδ0 : 0 ≤ δ)
    (htail : ∀ t : ℝ, δ ≤ t → v t =ᵐ[volume.restrict unitCube] w t),
    ∀ t : ℝ, δ < t → ENNReal.ofReal t < Tmax → u t = w t ∧ p t = q t :=
  @MethbokeAddon.WeakFouriermanB.maximal_front_tail_overlap_of_same_leray_hopf

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.maximal_front_tail_gluing_of_leray_hopf
example : ∀ (ν : ℝ) (a : Field) (u v : Velocity) (p : Pressure)
    (G : WeakGradientTrajectory) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (ha : SmoothSigmaZero a)
    (H : MaximalClassicalFront ν a u p Tmax)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G)
    (hcut : ENNReal.ofReal (cutoff (criticalL2Representative a) ν) < Tmax),
    ∃ (δ η : ℝ) (w : Velocity) (q : Pressure) (U : Velocity) (P : Pressure),
      cutoff (criticalL2Representative a) ν < δ ∧ δ < η ∧
      ENNReal.ofReal η < Tmax ∧ ClassicalTail ν δ w q ∧
      (∀ t : ℝ, δ ≤ t → v t =ᵐ[volume.restrict unitCube] w t) ∧
      (∀ t : ℝ, δ < t → ENNReal.ofReal t < Tmax → u t = w t ∧ p t = q t) ∧
      GlobalSmoothNSE ν a U P ∧
      (∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax → U t = u t ∧ P t = p t) ∧
      ∀ t : ℝ, η ≤ t → U t = w t ∧ P t = q t :=
  @MethbokeAddon.WeakFouriermanB.maximal_front_tail_gluing_of_leray_hopf

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_tail_overlap_of_same_leray_hopf"
#check @MethbokeAddon.WeakFouriermanB.maximal_front_tail_overlap_of_same_leray_hopf
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_front_tail_overlap_of_same_leray_hopf"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_tail_overlap_of_same_leray_hopf"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_front_tail_overlap_of_same_leray_hopf
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_front_tail_overlap_of_same_leray_hopf"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_tail_gluing_of_leray_hopf"
#check @MethbokeAddon.WeakFouriermanB.maximal_front_tail_gluing_of_leray_hopf
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.maximal_front_tail_gluing_of_leray_hopf"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.maximal_front_tail_gluing_of_leray_hopf"
#print axioms MethbokeAddon.WeakFouriermanB.maximal_front_tail_gluing_of_leray_hopf
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.maximal_front_tail_gluing_of_leray_hopf"
