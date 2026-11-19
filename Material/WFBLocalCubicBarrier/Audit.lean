import WFBLocalCubicBarrier.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory
open scoped Interval
open MethbokeAddon.WeakFouriermanB

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.localCubicTime_pos
example : ∀ {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 ≤ R),
    0 < localCubicTime κ R :=
  @MethbokeAddon.WeakFouriermanB.localCubicTime_pos

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.cubic_short_time_barrier
example : ∀ {y d : ℝ → ℝ} {κ R T : ℝ}
    (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (htime : T ≤ localCubicTime κ R)
    (hy : ContinuousOn y (Icc 0 T)) (hinit : y 0 ≤ R)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (d t) (Ici 0) t)
    (hcubic : ∀ t ∈ Ico 0 T, d t ≤ κ * (y t) ^ 3),
    ∀ t ∈ Icc 0 T, y t ≤ 2 * (R + 1) :=
  @MethbokeAddon.WeakFouriermanB.cubic_short_time_barrier

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.cubic_short_time_square_budget
example : ∀ {y d : ℝ → ℝ} {κ R T : ℝ}
    (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (htime : T ≤ localCubicTime κ R)
    (hy : ContinuousOn y (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t) (hinit : y 0 ≤ R)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (d t) (Ici 0) t)
    (hcubic : ∀ t ∈ Ico 0 T, d t ≤ κ * (y t) ^ 3),
    (∫ t in (0 : ℝ)..T, (y t) ^ 2) ≤ 4 * (R + 1) ^ 2 * T :=
  @MethbokeAddon.WeakFouriermanB.cubic_short_time_square_budget

-- Independent complete statement for MethbokeAddon.WeakFouriermanB.cubic_short_time_accumulation
example : ∀ {y z d : ℝ → ℝ} {ν κ R T : ℝ}
    (hν : 0 < ν) (hκ : 0 ≤ κ) (hR : 0 ≤ R) (hT : 0 ≤ T)
    (htime : T ≤ localCubicTime κ R)
    (hy : ContinuousOn y (Icc 0 T)) (hz : ContinuousOn z (Icc 0 T))
    (hd : ContinuousOn d (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t) (hinit : y 0 ≤ R)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (d t) (Ici 0) t)
    (hcubic : ∀ t ∈ Ico 0 T, d t + ν * (z t) ^ 2 ≤ κ * (y t) ^ 3),
    ∀ t ∈ Icc 0 T,
      y t + ν * (∫ s in (0 : ℝ)..t, (z s) ^ 2) ≤
        (R + 1) * Real.exp (κ * (4 * (R + 1) ^ 2 * T)) :=
  @MethbokeAddon.WeakFouriermanB.cubic_short_time_accumulation

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.localCubicTime_pos"
#check @MethbokeAddon.WeakFouriermanB.localCubicTime_pos
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.localCubicTime_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.localCubicTime_pos"
#print axioms MethbokeAddon.WeakFouriermanB.localCubicTime_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.localCubicTime_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.cubic_short_time_barrier"
#check @MethbokeAddon.WeakFouriermanB.cubic_short_time_barrier
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.cubic_short_time_barrier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.cubic_short_time_barrier"
#print axioms MethbokeAddon.WeakFouriermanB.cubic_short_time_barrier
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.cubic_short_time_barrier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.cubic_short_time_square_budget"
#check @MethbokeAddon.WeakFouriermanB.cubic_short_time_square_budget
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.cubic_short_time_square_budget"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.cubic_short_time_square_budget"
#print axioms MethbokeAddon.WeakFouriermanB.cubic_short_time_square_budget
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.cubic_short_time_square_budget"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.WeakFouriermanB.cubic_short_time_accumulation"
#check @MethbokeAddon.WeakFouriermanB.cubic_short_time_accumulation
#eval IO.println "TYPE_END:MethbokeAddon.WeakFouriermanB.cubic_short_time_accumulation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.WeakFouriermanB.cubic_short_time_accumulation"
#print axioms MethbokeAddon.WeakFouriermanB.cubic_short_time_accumulation
#eval IO.println "AXIOMS_END:MethbokeAddon.WeakFouriermanB.cubic_short_time_accumulation"
