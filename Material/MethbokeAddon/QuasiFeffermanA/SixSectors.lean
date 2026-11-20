import MethbokeAddon.QuasiFeffermanA.Contracts
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Linarith

/-!
# The six registered even Borel frequency sectors

Coordinates are ordered by decreasing absolute value, with smaller coordinate
index breaking ties. The permutation order is 012, 021, 102, 120, 201, 210.
The inequalities allocate every boundary point and the zero frequency exactly
once. Each sector is Borel, invariant under negation, and has nonempty interior.

The resulting real scalar masks are measurable, even, bounded, idempotent,
pairwise orthogonal, and sum to one pointwise. No Fourier L2 operator, real
inverse-Fourier range, weak-gradient transport or physical charge identity is
asserted here. Sharp masks are Borel symbols, not smooth multipliers.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory
open scoped BigOperators Topology

namespace MethbokeAddon.QuasiFeffermanA

/-- The registered six sectors, ordered by the permutations
`012, 021, 102, 120, 201, 210`; smaller indices win equal-magnitude ties. -/
def sixSector (i : Fin 6) : Set Space :=
  match i.val with
  | 0 => {ξ | |ξ 1| ≤ |ξ 0| ∧ |ξ 2| ≤ |ξ 1|}
  | 1 => {ξ | |ξ 2| ≤ |ξ 0| ∧ |ξ 1| < |ξ 2|}
  | 2 => {ξ | |ξ 0| < |ξ 1| ∧ |ξ 2| ≤ |ξ 0|}
  | 3 => {ξ | |ξ 2| ≤ |ξ 1| ∧ |ξ 0| < |ξ 2|}
  | 4 => {ξ | |ξ 0| < |ξ 2| ∧ |ξ 1| ≤ |ξ 0|}
  | _ => {ξ | |ξ 1| < |ξ 2| ∧ |ξ 0| < |ξ 1|}

private theorem continuous_abs_coordinate (j : Fin 3) :
    Continuous (fun ξ : Space => |ξ j|) :=
  (PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) j).abs

/-- Every registered sector is Borel measurable on the actual Euclidean space. -/
theorem measurableSet_sixSector (i : Fin 6) : MeasurableSet (sixSector i) := by
  have h (j : Fin 3) : Measurable (fun ξ : Space => |ξ j|) :=
    (continuous_abs_coordinate j).measurable
  fin_cases i
  · exact (measurableSet_le (h 1) (h 0)).inter (measurableSet_le (h 2) (h 1))
  · exact (measurableSet_le (h 2) (h 0)).inter (measurableSet_lt (h 1) (h 2))
  · exact (measurableSet_lt (h 0) (h 1)).inter (measurableSet_le (h 2) (h 0))
  · exact (measurableSet_le (h 2) (h 1)).inter (measurableSet_lt (h 0) (h 2))
  · exact (measurableSet_lt (h 0) (h 2)).inter (measurableSet_le (h 1) (h 0))
  · exact (measurableSet_lt (h 1) (h 2)).inter (measurableSet_lt (h 0) (h 1))

/-- Every frequency belongs to one of the six registered sectors. -/
theorem exists_mem_sixSector (ξ : Space) : ∃ i : Fin 6, ξ ∈ sixSector i := by
  by_cases h01 : |ξ 1| ≤ |ξ 0|
  · by_cases h12 : |ξ 2| ≤ |ξ 1|
    · exact ⟨0, h01, h12⟩
    · by_cases h02 : |ξ 2| ≤ |ξ 0|
      · exact ⟨1, h02, lt_of_not_ge h12⟩
      · exact ⟨4, lt_of_not_ge h02, h01⟩
  · by_cases h02 : |ξ 2| ≤ |ξ 0|
    · exact ⟨2, lt_of_not_ge h01, h02⟩
    · by_cases h12 : |ξ 2| ≤ |ξ 1|
      · exact ⟨3, h12, lt_of_not_ge h02⟩
      · exact ⟨5, lt_of_not_ge h12, lt_of_not_ge h01⟩

/-- Distinct sectors are exactly disjoint, including their tie boundaries. -/
theorem sixSector_disjoint {i j : Fin 6} (hij : i ≠ j) :
    Disjoint (sixSector i) (sixSector j) := by
  rw [Set.disjoint_left]
  intro ξ hi hj
  fin_cases i <;> fin_cases j <;>
    simp [sixSector] at hij hi hj <;>
    rcases hi with ⟨hi₁, hi₂⟩ <;>
    rcases hj with ⟨hj₁, hj₂⟩ <;> linarith

/-- Pairwise-disjoint formulation of the exact sector partition. -/
theorem sixSector_pairwiseDisjoint : Pairwise (fun i j : Fin 6 =>
    Disjoint (sixSector i) (sixSector j)) := by
  intro i j hij
  exact sixSector_disjoint hij

/-- Every frequency has exactly one sector index. -/
theorem existsUnique_mem_sixSector (ξ : Space) : ∃! i : Fin 6, ξ ∈ sixSector i := by
  obtain ⟨i, hi⟩ := exists_mem_sixSector ξ
  refine ⟨i, hi, ?_⟩
  intro j hj
  by_contra hji
  exact Set.disjoint_left.mp (sixSector_disjoint hji) hj hi

/-- The sector union is the whole Euclidean frequency space. -/
theorem iUnion_sixSector : (⋃ i : Fin 6, sixSector i) = univ := by
  ext ξ
  simp only [mem_iUnion, mem_univ, iff_true]
  exact exists_mem_sixSector ξ

/-- Antipodal symmetry follows from actual absolute coordinate values. -/
theorem mem_sixSector_neg_iff (i : Fin 6) (ξ : Space) :
    -ξ ∈ sixSector i ↔ ξ ∈ sixSector i := by
  have h (j : Fin 3) : |(-ξ) j| = |ξ j| := by simp
  fin_cases i <;> simp [sixSector, h]

/-- The registered tie rule allocates zero exactly to the first sector. -/
@[simp] theorem zero_mem_sixSector_iff (i : Fin 6) :
    (0 : Space) ∈ sixSector i ↔ i = 0 := by
  fin_cases i <;> norm_num [sixSector]

private def strictSixSector (i : Fin 6) : Set Space :=
  match i.val with
  | 0 => {ξ | |ξ 1| < |ξ 0| ∧ |ξ 2| < |ξ 1|}
  | 1 => {ξ | |ξ 2| < |ξ 0| ∧ |ξ 1| < |ξ 2|}
  | 2 => {ξ | |ξ 0| < |ξ 1| ∧ |ξ 2| < |ξ 0|}
  | 3 => {ξ | |ξ 2| < |ξ 1| ∧ |ξ 0| < |ξ 2|}
  | 4 => {ξ | |ξ 0| < |ξ 2| ∧ |ξ 1| < |ξ 0|}
  | _ => {ξ | |ξ 1| < |ξ 2| ∧ |ξ 0| < |ξ 1|}

private theorem isOpen_strictSixSector (i : Fin 6) : IsOpen (strictSixSector i) := by
  have h := continuous_abs_coordinate
  fin_cases i
  · exact (isOpen_lt (h 1) (h 0)).inter (isOpen_lt (h 2) (h 1))
  · exact (isOpen_lt (h 2) (h 0)).inter (isOpen_lt (h 1) (h 2))
  · exact (isOpen_lt (h 0) (h 1)).inter (isOpen_lt (h 2) (h 0))
  · exact (isOpen_lt (h 2) (h 1)).inter (isOpen_lt (h 0) (h 2))
  · exact (isOpen_lt (h 0) (h 2)).inter (isOpen_lt (h 1) (h 0))
  · exact (isOpen_lt (h 1) (h 2)).inter (isOpen_lt (h 0) (h 1))

private theorem strictSixSector_subset (i : Fin 6) : strictSixSector i ⊆ sixSector i := by
  intro ξ hξ
  fin_cases i <;> simp only [strictSixSector, sixSector, mem_setOf_eq] at hξ ⊢ <;>
    constructor <;> linarith [hξ.1, hξ.2]

private def sixSectorInteriorPoint (i : Fin 6) : Space :=
  WithLp.toLp 2 <| match i.val with
  | 0 => ![3, 2, 1]
  | 1 => ![3, 1, 2]
  | 2 => ![2, 3, 1]
  | 3 => ![1, 3, 2]
  | 4 => ![2, 1, 3]
  | _ => ![1, 2, 3]

private theorem sixSectorInteriorPoint_mem (i : Fin 6) :
    sixSectorInteriorPoint i ∈ strictSixSector i := by
  fin_cases i <;> norm_num [sixSectorInteriorPoint, strictSixSector,
    Matrix.cons_val_two]

/-- Every sector contains a nonempty open strict-order region. -/
theorem sixSector_interior_nonempty (i : Fin 6) : (interior (sixSector i)).Nonempty := by
  refine ⟨sixSectorInteriorPoint i, ?_⟩
  exact ((isOpen_strictSixSector i).subset_interior_iff.mpr
    (strictSixSector_subset i)) (sixSectorInteriorPoint_mem i)

/-- The actual real scalar indicator of a registered sector. -/
def sixSectorMask (i : Fin 6) : Space → ℝ :=
  (sixSector i).indicator (fun _ => 1)

/-- The sharp masks are measurable despite their discontinuous boundaries. -/
theorem measurable_sixSectorMask (i : Fin 6) : Measurable (sixSectorMask i) :=
  measurable_const.indicator (measurableSet_sixSector i)

/-- Each mask preserves antipodal symmetry pointwise. -/
theorem sixSectorMask_neg (i : Fin 6) (ξ : Space) :
    sixSectorMask i (-ξ) = sixSectorMask i ξ := by
  classical
  simp only [sixSectorMask, Set.indicator_apply, mem_sixSector_neg_iff]

/-- The masks satisfy the bounded-multiplier norm bound one. -/
theorem norm_sixSectorMask_le_one (i : Fin 6) (ξ : Space) :
    ‖sixSectorMask i ξ‖ ≤ 1 := by
  by_cases h : ξ ∈ sixSector i <;> simp [sixSectorMask, h]

/-- Pointwise idempotence of the literal indicator symbols. -/
theorem sixSectorMask_sq (i : Fin 6) (ξ : Space) :
    (sixSectorMask i ξ) ^ 2 = sixSectorMask i ξ := by
  by_cases h : ξ ∈ sixSector i <;> simp [sixSectorMask, h]

/-- Distinct masks have zero pointwise product. -/
theorem sixSectorMask_mul_eq_zero {i j : Fin 6} (hij : i ≠ j) (ξ : Space) :
    sixSectorMask i ξ * sixSectorMask j ξ = 0 := by
  by_cases hi : ξ ∈ sixSector i
  · have hj : ξ ∉ sixSector j := by
      intro hj
      exact Set.disjoint_left.mp (sixSector_disjoint hij) hi hj
    simp [sixSectorMask, hi, hj]
  · simp [sixSectorMask, hi]

/-- Exact pointwise reconstruction, including ties and the zero frequency. -/
theorem sum_sixSectorMask (ξ : Space) : ∑ i : Fin 6, sixSectorMask i ξ = 1 := by
  classical
  obtain ⟨i, hi, hunique⟩ := existsUnique_mem_sixSector ξ
  rw [Finset.sum_eq_single i]
  · simp [sixSectorMask, hi]
  · intro j _ hji
    have hj : ξ ∉ sixSector j := by
      intro hj
      exact hji (hunique j hj)
    simp [sixSectorMask, hj]
  · intro hi_not
    exact (hi_not (Finset.mem_univ i)).elim

end MethbokeAddon.QuasiFeffermanA
