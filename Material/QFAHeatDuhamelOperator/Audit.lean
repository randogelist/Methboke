import QFAHeatDuhamelOperator.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set MeasureTheory MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.HeatSemigroup
open MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator
open scoped NNReal ENNReal Topology

noncomputable section

/- The carrier is the actual forcing quotient and continuous physical path space. -/
example (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T) :
    Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T)) →L[ℝ]
      ContinuousMap (Icc (0 : ℝ) T) SpatialL2 :=
  duhamelL2Operator ν T hT

example (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (F : Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : Icc (0 : ℝ) T) :
    duhamelL2Operator ν T hT F t =
      ∫ s in (0 : ℝ)..(t : ℝ), heatL2 ν ((t : ℝ) - s).toNNReal (F s) :=
  duhamelL2Operator_apply ν T hT F t

example (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T) :
    ‖duhamelL2Operator ν T hT‖ ≤ Real.sqrt T :=
  duhamelL2Operator_norm_le ν T hT

example (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (F : Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T))) :
    duhamelL2Operator ν T hT F ⟨0, le_rfl, hT⟩ = (0 : SpatialL2) :=
  duhamelL2Operator_zero_trace ν T hT F

/- Every actual MemLp representative produces the same literal response. -/
example (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → SpatialL2) (hf : MemLp f 2 (volume.restrict (Ioc (0 : ℝ) T)))
    (t : Icc (0 : ℝ) T) :
    duhamelL2Operator ν T hT (hf.toLp f) t =
      ∫ s in (0 : ℝ)..(t : ℝ), heatL2 ν ((t : ℝ) - s).toNNReal (f s) :=
  duhamelL2Operator_toLp_apply ν T hT f hf t

/- One bounded operator carries the literal integral and initial trace for
every forcing class, with the exact sqrt(T) bound. -/
example (ν : ℝ≥0) (T : ℝ) (hT : 0 ≤ T) :
    ∃ K : Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T)) →L[ℝ]
        ContinuousMap (Icc (0 : ℝ) T) SpatialL2,
      ‖K‖ ≤ Real.sqrt T ∧
      ∀ F : Lp SpatialL2 2 (volume.restrict (Ioc (0 : ℝ) T)),
        K F ⟨0, le_rfl, hT⟩ = 0 ∧
        ∀ t : Icc (0 : ℝ) T,
          K F t = (∫ s in (0 : ℝ)..(t : ℝ),
            heatL2 ν ((t : ℝ) - s).toNNReal (F s)) := by
  refine ⟨duhamelL2Operator ν T hT, duhamelL2Operator_norm_le ν T hT, ?_⟩
  intro F
  exact ⟨duhamelL2Operator_zero_trace ν T hT F,
    fun t => duhamelL2Operator_apply ν T hT F t⟩

/- The zero-horizon case is included in the operator estimate itself. -/
example (ν : ℝ≥0) : duhamelL2Operator ν 0 le_rfl = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm
  · simpa only [Real.sqrt_zero] using duhamelL2Operator_norm_le ν 0 le_rfl
  · exact norm_nonneg _

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_apply"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_norm_le"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_norm_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_norm_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_norm_le"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_norm_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_norm_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_zero_trace"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_zero_trace
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_zero_trace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_zero_trace"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_zero_trace
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_zero_trace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_toLp_apply"
#check @MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_toLp_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_toLp_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_toLp_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_toLp_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator.duhamelL2Operator_toLp_apply"

