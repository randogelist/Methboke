import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.Constructions.SumProd

/-!
# Locality of finite sums with disjoint closed carriers

This is the support-locality part of the finite-family construction (F05).
At a point of one closed carrier, including its boundary, every other summand
vanishes on a common neighborhood. Outside all carriers the sum vanishes on
a neighborhood. Compact carriers in Hausdorff spaces are a special case.

The spacetime lemmas require one spatial carrier for every time slice. They
therefore yield a genuine spacetime germ equality, not only equality on one
time slice. These statements do not assert an NSE seed or family witness.
-/

open Filter Set
open scoped BigOperators Topology

namespace MethbokeAddon.FeffermanFamily

section ZeroCarrier

variable {X A : Type*} [TopologicalSpace X] [Zero A]

/-- A function supported in a closed carrier is locally zero off that carrier. -/
theorem supported_eventuallyEq_zero_of_not_mem
    {K : Set X} {f : X → A} (hclosed : IsClosed K)
    (hzero : ∀ x, x ∉ K → f x = 0) {x : X} (hx : x ∉ K) :
    f =ᶠ[𝓝 x] (fun _ => 0) := by
  have houtside : ∀ᶠ y in 𝓝 x, y ∉ K := hclosed.compl_mem_nhds hx
  exact houtside.mono fun y hy => hzero y hy

end ZeroCarrier

section FiniteSum

variable {ι X A : Type*} [Fintype ι] [AddCommMonoid A]

/-- At an active carrier, a finite supported sum is exactly its active term. -/
theorem finite_sum_eq_active_of_disjoint_carriers
    {K : ι → Set X} {f : ι → X → A}
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hzero : ∀ i x, x ∉ K i → f i x = 0)
    {i : ι} {x : X} (hxi : x ∈ K i) :
    (∑ j, f j x) = f i x := by
  classical
  apply Finset.sum_eq_single i
  · intro j _ hji
    apply hzero j x
    intro hxj
    exact Set.disjoint_left.1 (hdisjoint hji) hxj hxi
  · simp

/-- Outside all carriers, every term and hence the finite sum is zero. -/
theorem finite_sum_eq_zero_of_outside_carriers
    {K : ι → Set X} {f : ι → X → A}
    (hzero : ∀ i x, x ∉ K i → f i x = 0)
    {x : X} (hx : ∀ i, x ∉ K i) :
    (∑ i, f i x) = 0 := by
  exact Finset.sum_eq_zero fun i _ => hzero i x (hx i)

variable [TopologicalSpace X]

/-- A finite sum equals its active summand on a neighborhood, even at the
boundary of that summand's closed carrier. -/
theorem finite_sum_eventuallyEq_active_of_disjoint_closed_carriers
    {K : ι → Set X} {f : ι → X → A}
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hzero : ∀ i x, x ∉ K i → f i x = 0)
    {i : ι} {x : X} (hxi : x ∈ K i) :
    (fun y => ∑ j, f j y) =ᶠ[𝓝 x] f i := by
  classical
  have hjzero : ∀ j, ∀ᶠ y in 𝓝 x, j ≠ i → f j y = 0 := by
    intro j
    by_cases hji : j = i
    · exact Filter.Eventually.of_forall fun _ h => (h hji).elim
    · have hxj : x ∉ K j := by
        intro hxj
        exact Set.disjoint_left.1 (hdisjoint hji) hxj hxi
      exact (supported_eventuallyEq_zero_of_not_mem
        (hclosed j) (hzero j) hxj).mono fun _ hy _ => hy
  have hall : ∀ᶠ y in 𝓝 x, ∀ j, j ≠ i → f j y = 0 :=
    Filter.eventually_all.2 hjzero
  exact hall.mono fun y hy =>
    Finset.sum_eq_single i (fun j _ hji => hy j hji) (by simp)

/-- A finite sum is locally zero outside all of its closed carriers. -/
theorem finite_sum_eventuallyEq_zero_of_outside_closed_carriers
    {K : ι → Set X} {f : ι → X → A}
    (hclosed : ∀ i, IsClosed (K i))
    (hzero : ∀ i x, x ∉ K i → f i x = 0)
    {x : X} (hx : ∀ i, x ∉ K i) :
    (fun y => ∑ i, f i y) =ᶠ[𝓝 x] (fun _ => 0) := by
  have hjzero : ∀ i, ∀ᶠ y in 𝓝 x, f i y = 0 :=
    fun i => supported_eventuallyEq_zero_of_not_mem (hclosed i) (hzero i) (hx i)
  have hall : ∀ᶠ y in 𝓝 x, ∀ i, f i y = 0 := Filter.eventually_all.2 hjzero
  exact hall.mono fun _ hy => Finset.sum_eq_zero fun i _ => hy i

/-- At every point, a finite supported sum is locally one summand or zero. -/
theorem finite_sum_locally_active_or_zero
    {K : ι → Set X} {f : ι → X → A}
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hzero : ∀ i x, x ∉ K i → f i x = 0) (x : X) :
    (∃ i, x ∈ K i ∧ (fun y => ∑ j, f j y) =ᶠ[𝓝 x] f i) ∨
      (fun y => ∑ j, f j y) =ᶠ[𝓝 x] (fun _ => 0) := by
  classical
  by_cases hx : ∃ i, x ∈ K i
  · obtain ⟨i, hxi⟩ := hx
    exact Or.inl ⟨i, hxi,
      finite_sum_eventuallyEq_active_of_disjoint_closed_carriers
        hclosed hdisjoint hzero hxi⟩
  · exact Or.inr (finite_sum_eventuallyEq_zero_of_outside_closed_carriers
      hclosed hzero (fun i hi => hx ⟨i, hi⟩))

end FiniteSum

section Spacetime

variable {ι T X A : Type*} [Fintype ι]
variable [TopologicalSpace T] [TopologicalSpace X] [AddCommMonoid A]

/-- Uniform spatial support gives the active-copy identity as a spacetime germ. -/
theorem finite_sum_spacetime_eventuallyEq_active
    {K : ι → Set X} {f : ι → T → X → A}
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hzero : ∀ i t x, x ∉ K i → f i t x = 0)
    {i : ι} {x : X} (hxi : x ∈ K i) (t : T) :
    (fun z : T × X => ∑ j, f j z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => f i z.1 z.2) := by
  apply finite_sum_eventuallyEq_active_of_disjoint_closed_carriers
    (K := fun j => Prod.snd ⁻¹' K j)
    (f := fun j (z : T × X) => f j z.1 z.2) (i := i) (x := (t, x))
  · intro j
    exact (hclosed j).preimage continuous_snd
  · intro j k hjk
    exact Set.disjoint_left.2 fun _ hzj hzk =>
      Set.disjoint_left.1 (hdisjoint hjk) hzj hzk
  · intro j z hz
    exact hzero j z.1 z.2 hz
  · exact hxi

/-- Uniform spatial support gives a zero spacetime germ outside all carriers. -/
theorem finite_sum_spacetime_eventuallyEq_zero
    {K : ι → Set X} {f : ι → T → X → A}
    (hclosed : ∀ i, IsClosed (K i))
    (hzero : ∀ i t x, x ∉ K i → f i t x = 0)
    {x : X} (hx : ∀ i, x ∉ K i) (t : T) :
    (fun z : T × X => ∑ j, f j z.1 z.2) =ᶠ[𝓝 (t, x)] (fun _ => 0) := by
  apply finite_sum_eventuallyEq_zero_of_outside_closed_carriers
    (K := fun j => Prod.snd ⁻¹' K j)
    (f := fun j (z : T × X) => f j z.1 z.2) (x := (t, x))
  · intro j
    exact (hclosed j).preimage continuous_snd
  · intro j z hz
    exact hzero j z.1 z.2 hz
  · exact hx

end Spacetime

end MethbokeAddon.FeffermanFamily
