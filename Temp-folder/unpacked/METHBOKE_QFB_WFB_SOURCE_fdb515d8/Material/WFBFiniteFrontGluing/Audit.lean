import WFBFiniteFrontGluing.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff Topology
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.finite_front_splice_contDiffOn
example : ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ T S η : ℝ) (f g : ℝ → Vec → E) (hδη : δ < η) (hηT : η < T)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) (initialFrontSpacetime T))
    (hg : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => g z.1 z.2)
      {z : ℝ × Vec | z.1 ∈ Ioo δ S})
    (hagree : ∀ r ∈ Ioo δ T, f r = g r),
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => finiteCapSplice η f g z.1 z.2)
      (initialFrontSpacetime S) :=
  @MethbokeAddon.WeakFouriermanB.finite_front_splice_contDiffOn

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.initial_front_extend_from_restart
example : ∀ (ν T s h : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (hν : 0 < ν) (H : InitialClassicalFront ν T a u p)
    (hs : s ∈ Ico (0 : ℝ) T) (hh : 0 < h)
    (K : InitialClassicalFront ν h (u s) v q) (hextend : T < s + h),
    ∃ (U : Velocity) (P : Pressure), InitialClassicalFront ν (s + h) a U P ∧
      (∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r) ∧
      ∀ r ∈ Ico ((s + T) / 2) (s + h),
        U r = v (r - s) ∧ P r = q (r - s) :=
  @MethbokeAddon.WeakFouriermanB.initial_front_extend_from_restart

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finite_front_splice_contDiffOn"
#check @MethbokeAddon.WeakFouriermanB.finite_front_splice_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finite_front_splice_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finite_front_splice_contDiffOn"
#print axioms MethbokeAddon.WeakFouriermanB.finite_front_splice_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finite_front_splice_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_extend_from_restart"
#check @MethbokeAddon.WeakFouriermanB.initial_front_extend_from_restart
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.initial_front_extend_from_restart"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.initial_front_extend_from_restart"
#print axioms MethbokeAddon.WeakFouriermanB.initial_front_extend_from_restart
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.initial_front_extend_from_restart"
