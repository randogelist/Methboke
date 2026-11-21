import QFASixSectors.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section
open Set MeasureTheory
open scoped BigOperators

namespace QFASixSectors.ExpectedTypes
open MethbokeAddon.QuasiFeffermanA

-- Concrete R3 carrier and literal registered tie-breaking partition.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example (i : Fin 6) : sixSector i =
    match i.val with
    | 0 => {ξ : EuclideanSpace ℝ (Fin 3) | |ξ 1| ≤ |ξ 0| ∧ |ξ 2| ≤ |ξ 1|}
    | 1 => {ξ : EuclideanSpace ℝ (Fin 3) | |ξ 2| ≤ |ξ 0| ∧ |ξ 1| < |ξ 2|}
    | 2 => {ξ : EuclideanSpace ℝ (Fin 3) | |ξ 0| < |ξ 1| ∧ |ξ 2| ≤ |ξ 0|}
    | 3 => {ξ : EuclideanSpace ℝ (Fin 3) | |ξ 2| ≤ |ξ 1| ∧ |ξ 0| < |ξ 2|}
    | 4 => {ξ : EuclideanSpace ℝ (Fin 3) | |ξ 0| < |ξ 2| ∧ |ξ 1| ≤ |ξ 0|}
    | _ => {ξ : EuclideanSpace ℝ (Fin 3) | |ξ 1| < |ξ 2| ∧ |ξ 0| < |ξ 1|} := rfl

example (i : Fin 6) : MeasurableSet (sixSector i) :=
  measurableSet_sixSector i
example (ξ : EuclideanSpace ℝ (Fin 3)) : ∃ i : Fin 6, ξ ∈ sixSector i :=
  exists_mem_sixSector ξ
example (i j : Fin 6) (hij : i ≠ j) : Disjoint (sixSector i) (sixSector j) :=
  sixSector_disjoint hij
example : Pairwise (fun i j : Fin 6 => Disjoint (sixSector i) (sixSector j)) :=
  sixSector_pairwiseDisjoint
example (ξ : EuclideanSpace ℝ (Fin 3)) : ∃! i : Fin 6, ξ ∈ sixSector i :=
  existsUnique_mem_sixSector ξ
example : (⋃ i : Fin 6, sixSector i) = (Set.univ : Set (EuclideanSpace ℝ (Fin 3))) :=
  iUnion_sixSector
example (i : Fin 6) (ξ : EuclideanSpace ℝ (Fin 3)) :
    -ξ ∈ sixSector i ↔ ξ ∈ sixSector i :=
  mem_sixSector_neg_iff i ξ
example (i : Fin 6) : (0 : EuclideanSpace ℝ (Fin 3)) ∈ sixSector i ↔ i = 0 :=
  zero_mem_sixSector_iff i
example (i : Fin 6) : (interior (sixSector i)).Nonempty :=
  sixSector_interior_nonempty i

-- Literal measurable indicators, not supplied abstract masks or smooth symbols.
example (i : Fin 6) : sixSectorMask i =
    (sixSector i).indicator (fun _ : EuclideanSpace ℝ (Fin 3) => (1 : ℝ)) := rfl
example (i : Fin 6) : Measurable (sixSectorMask i) := measurable_sixSectorMask i
example (i : Fin 6) (ξ : EuclideanSpace ℝ (Fin 3)) :
    sixSectorMask i (-ξ) = sixSectorMask i ξ := sixSectorMask_neg i ξ
example (i : Fin 6) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖sixSectorMask i ξ‖ ≤ 1 := norm_sixSectorMask_le_one i ξ
example (i : Fin 6) (ξ : EuclideanSpace ℝ (Fin 3)) :
    sixSectorMask i ξ ^ 2 = sixSectorMask i ξ := sixSectorMask_sq i ξ
example (i j : Fin 6) (hij : i ≠ j) (ξ : EuclideanSpace ℝ (Fin 3)) :
    sixSectorMask i ξ * sixSectorMask j ξ = 0 := sixSectorMask_mul_eq_zero hij ξ
example (ξ : EuclideanSpace ℝ (Fin 3)) : ∑ i : Fin 6, sixSectorMask i ξ = 1 :=
  sum_sixSectorMask ξ

end QFASixSectors.ExpectedTypes

-- Named reports execute only in authorized external verification.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSector"
#check @MethbokeAddon.QuasiFeffermanA.sixSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSector"
#print axioms MethbokeAddon.QuasiFeffermanA.sixSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.measurableSet_sixSector"
#check @MethbokeAddon.QuasiFeffermanA.measurableSet_sixSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.measurableSet_sixSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.measurableSet_sixSector"
#print axioms MethbokeAddon.QuasiFeffermanA.measurableSet_sixSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.measurableSet_sixSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.exists_mem_sixSector"
#check @MethbokeAddon.QuasiFeffermanA.exists_mem_sixSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.exists_mem_sixSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.exists_mem_sixSector"
#print axioms MethbokeAddon.QuasiFeffermanA.exists_mem_sixSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.exists_mem_sixSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSector_disjoint"
#check @MethbokeAddon.QuasiFeffermanA.sixSector_disjoint
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixSector_disjoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSector_disjoint"
#print axioms MethbokeAddon.QuasiFeffermanA.sixSector_disjoint
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixSector_disjoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSector_pairwiseDisjoint"
#check @MethbokeAddon.QuasiFeffermanA.sixSector_pairwiseDisjoint
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixSector_pairwiseDisjoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSector_pairwiseDisjoint"
#print axioms MethbokeAddon.QuasiFeffermanA.sixSector_pairwiseDisjoint
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixSector_pairwiseDisjoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.existsUnique_mem_sixSector"
#check @MethbokeAddon.QuasiFeffermanA.existsUnique_mem_sixSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.existsUnique_mem_sixSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.existsUnique_mem_sixSector"
#print axioms MethbokeAddon.QuasiFeffermanA.existsUnique_mem_sixSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.existsUnique_mem_sixSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.iUnion_sixSector"
#check @MethbokeAddon.QuasiFeffermanA.iUnion_sixSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.iUnion_sixSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.iUnion_sixSector"
#print axioms MethbokeAddon.QuasiFeffermanA.iUnion_sixSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.iUnion_sixSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_sixSector_neg_iff"
#check @MethbokeAddon.QuasiFeffermanA.mem_sixSector_neg_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.mem_sixSector_neg_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.mem_sixSector_neg_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.mem_sixSector_neg_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.mem_sixSector_neg_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.zero_mem_sixSector_iff"
#check @MethbokeAddon.QuasiFeffermanA.zero_mem_sixSector_iff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.zero_mem_sixSector_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.zero_mem_sixSector_iff"
#print axioms MethbokeAddon.QuasiFeffermanA.zero_mem_sixSector_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.zero_mem_sixSector_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSector_interior_nonempty"
#check @MethbokeAddon.QuasiFeffermanA.sixSector_interior_nonempty
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixSector_interior_nonempty"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSector_interior_nonempty"
#print axioms MethbokeAddon.QuasiFeffermanA.sixSector_interior_nonempty
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixSector_interior_nonempty"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSectorMask"
#check @MethbokeAddon.QuasiFeffermanA.sixSectorMask
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixSectorMask"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSectorMask"
#print axioms MethbokeAddon.QuasiFeffermanA.sixSectorMask
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixSectorMask"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.measurable_sixSectorMask"
#check @MethbokeAddon.QuasiFeffermanA.measurable_sixSectorMask
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.measurable_sixSectorMask"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.measurable_sixSectorMask"
#print axioms MethbokeAddon.QuasiFeffermanA.measurable_sixSectorMask
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.measurable_sixSectorMask"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSectorMask_neg"
#check @MethbokeAddon.QuasiFeffermanA.sixSectorMask_neg
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixSectorMask_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSectorMask_neg"
#print axioms MethbokeAddon.QuasiFeffermanA.sixSectorMask_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixSectorMask_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.norm_sixSectorMask_le_one"
#check @MethbokeAddon.QuasiFeffermanA.norm_sixSectorMask_le_one
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.norm_sixSectorMask_le_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.norm_sixSectorMask_le_one"
#print axioms MethbokeAddon.QuasiFeffermanA.norm_sixSectorMask_le_one
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.norm_sixSectorMask_le_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSectorMask_sq"
#check @MethbokeAddon.QuasiFeffermanA.sixSectorMask_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixSectorMask_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSectorMask_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.sixSectorMask_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixSectorMask_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSectorMask_mul_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.sixSectorMask_mul_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sixSectorMask_mul_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sixSectorMask_mul_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.sixSectorMask_mul_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sixSectorMask_mul_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_sixSectorMask"
#check @MethbokeAddon.QuasiFeffermanA.sum_sixSectorMask
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sum_sixSectorMask"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_sixSectorMask"
#print axioms MethbokeAddon.QuasiFeffermanA.sum_sixSectorMask
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sum_sixSectorMask"
