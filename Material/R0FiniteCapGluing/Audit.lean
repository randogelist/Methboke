import R0FiniteCapGluing.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure QuasiFeffermanB MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff ENNReal Topology Interval

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_left
example : ∀ {E : Type*}
    (η : ℝ) (f g : ℝ → E) {t : ℝ} (ht : t < η),
    finiteCapSplice η f g =ᶠ[𝓝 t] f :=
  @MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_left

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_right
example : ∀ {E : Type*}
    (δ T η : ℝ) (f g : ℝ → E) (hηT : η < T)
    (hagree : ∀ r ∈ Ioo δ T, f r = g r) {t : ℝ} (ht : δ < t),
    finiteCapSplice η f g =ᶠ[𝓝 t] g :=
  @MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_right

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finiteCapSplice_contDiffOn
example : ∀ {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (δ T η : ℝ) (f g : ℝ → Vec → E) (hδη : δ < η) (hηT : η < T)
    (hf : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => f z.1 z.2) (initialFrontSpacetime T))
    (hg : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => g z.1 z.2) (tailSpacetime δ))
    (hagree : ∀ r ∈ Ioo δ T, f r = g r),
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => finiteCapSplice η f g z.1 z.2)
      forwardSpacetime :=
  @MethbokeAddon.WeakFouriermanB.finiteCapSplice_contDiffOn

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finite_cap_splice_global_smooth
example : ∀ (ν T δ η : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (H : InitialClassicalFront ν T a u p) (K : ClassicalTail ν δ v q)
    (hη0 : 0 < η) (hδη : δ < η) (hηT : η < T)
    (huv : ∀ r ∈ Ioo δ T, u r = v r)
    (hpq : ∀ r ∈ Ioo δ T, p r = q r),
    GlobalSmoothNSE ν a (finiteCapSplice η u v) (finiteCapSplice η p q) :=
  @MethbokeAddon.WeakFouriermanB.finite_cap_splice_global_smooth

-- Exact independently stated type: MethbokeAddon.WeakFouriermanB.finite_cap_gluing
example : ∀ (ν T δ : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (H : InitialClassicalFront ν T a u p) (K : ClassicalTail ν δ v q)
    (hδ0 : 0 ≤ δ) (hδT : δ < T)
    (huv : ∀ r ∈ Ioo δ T, u r = v r)
    (hpq : ∀ r ∈ Ioo δ T, p r = q r),
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      (∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r) ∧
      ∀ r : ℝ, (δ + T) / 2 ≤ r → U r = v r ∧ P r = q r :=
  @MethbokeAddon.WeakFouriermanB.finite_cap_gluing

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_left"
#check @MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_left
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_left"
#print axioms MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_left
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_right"
#check @MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_right
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_right"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_right"
#print axioms MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_right
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finiteCapSplice_eventually_right"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finiteCapSplice_contDiffOn"
#check @MethbokeAddon.WeakFouriermanB.finiteCapSplice_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finiteCapSplice_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finiteCapSplice_contDiffOn"
#print axioms MethbokeAddon.WeakFouriermanB.finiteCapSplice_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finiteCapSplice_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finite_cap_splice_global_smooth"
#check @MethbokeAddon.WeakFouriermanB.finite_cap_splice_global_smooth
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finite_cap_splice_global_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finite_cap_splice_global_smooth"
#print axioms MethbokeAddon.WeakFouriermanB.finite_cap_splice_global_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finite_cap_splice_global_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.finite_cap_gluing"
#check @MethbokeAddon.WeakFouriermanB.finite_cap_gluing
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.finite_cap_gluing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.finite_cap_gluing"
#print axioms MethbokeAddon.WeakFouriermanB.finite_cap_gluing
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.finite_cap_gluing"

