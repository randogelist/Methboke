import FeffermanFamilyFoundation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-!
Independent consumer types and literal-contract checks for the first T3 family
layer. All audits must execute freshly in authorized external cached CI.
The target family existence proposition is only defined, never assumed globally.
-/

open Filter Set MeasureTheory SingularClosure
open MethbokeAddon.FeffermanFamily
open scoped BigOperators Topology ContDiff

namespace FeffermanFamilyFoundation.TypeChecks

universe u v w

section LocalGrowth

variable {X : Type u} {E : Type v}
variable [PseudoMetricSpace X] [NormedAddCommGroup E]

-- Literal quantitative meaning, independently expanded rather than just named.
example (U : ℝ → X → E) (a : X) (T : ℝ) :
    LocalVelocityBlowup U a T ↔
      ∀ M : ℝ, 0 < M → ∀ ε : ℝ, 0 < ε → ∀ δ : ℝ, 0 < δ →
        ∃ t : ℝ, ∃ x : X,
          0 < t ∧ t < T ∧ T - t < δ ∧ dist x a < ε ∧ M < ‖U t x‖ := Iff.rfl

example {U : ℝ → X → E} {a : X} {T : ℝ}
    (h : LocalVelocityBlowup U a T) : 0 < T :=
  LocalVelocityBlowup.terminal_pos h

example {U V : ℝ → X → E} {a : X} {T : ℝ}
    (h : LocalVelocityBlowup U a T)
    (heq : ∀ t, 0 < t → t < T → ∀ x, V t x = U t x) :
    LocalVelocityBlowup V a T :=
  LocalVelocityBlowup.congr_on_left h heq

example {U : ℝ → X → E} {a : X} {T : ℝ}
    (h : LocalVelocityBlowup U a T) :
    ¬ ∃ ε : ℝ, 0 < ε ∧ ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ t x, 0 < t → t < T → T - t < δ → dist x a < ε → ‖U t x‖ ≤ C :=
  LocalVelocityBlowup.not_locally_bounded h

example {U : ℝ → X → E} {a : X} {T : ℝ}
    (h : LocalVelocityBlowup U a T) :
    ¬ ContinuousAt (fun z : ℝ × X => U z.1 z.2) (T, a) :=
  LocalVelocityBlowup.not_continuousAt h

example {U : ℝ → X → E} {a : X} {T : ℝ}
    (h : LocalVelocityBlowup U a T) (V : ℝ → X → E)
    (heq : ∀ t, 0 < t → t < T → ∀ x, V t x = U t x) :
    ¬ ContinuousAt (fun z : ℝ × X => V z.1 z.2) (T, a) :=
  LocalVelocityBlowup.not_continuousAt_of_agrees h V heq

example {U : ℝ → X → E} {a : X} {T : ℝ}
    (t : ℕ → ℝ) (x : ℕ → X)
    (ht : ∀ n, 0 < t n ∧ t n < T)
    (htend : Tendsto t atTop (𝓝 T))
    (hxend : Tendsto x atTop (𝓝 a))
    (hlarge : Tendsto (fun n => ‖U (t n) (x n)‖) atTop atTop) :
    LocalVelocityBlowup U a T :=
  LocalVelocityBlowup.of_sequence t x ht htend hxend hlarge

example (U : ℝ → X → E) (K : Set X) (hK : IsCompact K) (T : ℝ)
    (t : ℕ → ℝ) (x : ℕ → X)
    (ht : ∀ n, 0 < t n ∧ t n < T)
    (htend : Tendsto t atTop (𝓝 T))
    (hxK : ∀ n, x n ∈ K)
    (hlarge : Tendsto (fun n => ‖U (t n) (x n)‖) atTop atTop) :
    ∃ a ∈ K, LocalVelocityBlowup U a T :=
  exists_localVelocityBlowup_of_compact_sequence U K hK T t x ht htend hxK hlarge

end LocalGrowth

section Carriers

example {X A : Type*} [TopologicalSpace X] [Zero A]
    {K : Set X} {f : X → A} (hclosed : IsClosed K)
    (hzero : ∀ x, x ∉ K → f x = 0) {x : X} (hx : x ∉ K) :
    f =ᶠ[𝓝 x] (fun _ => 0) :=
  supported_eventuallyEq_zero_of_not_mem hclosed hzero hx

example {ι X A : Type*} [Fintype ι] [AddCommMonoid A]
    {K : ι → Set X} {f : ι → X → A}
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hzero : ∀ i x, x ∉ K i → f i x = 0)
    {i : ι} {x : X} (hxi : x ∈ K i) :
    (∑ j, f j x) = f i x :=
  finite_sum_eq_active_of_disjoint_carriers hdisjoint hzero hxi

example {ι X A : Type*} [Fintype ι] [AddCommMonoid A]
    {K : ι → Set X} {f : ι → X → A}
    (hzero : ∀ i x, x ∉ K i → f i x = 0)
    {x : X} (hx : ∀ i, x ∉ K i) : (∑ i, f i x) = 0 :=
  finite_sum_eq_zero_of_outside_carriers hzero hx

example {ι X A : Type*} [Fintype ι] [AddCommMonoid A] [TopologicalSpace X]
    {K : ι → Set X} {f : ι → X → A}
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hzero : ∀ i x, x ∉ K i → f i x = 0)
    {i : ι} {x : X} (hxi : x ∈ K i) :
    (fun y => ∑ j, f j y) =ᶠ[𝓝 x] f i :=
  finite_sum_eventuallyEq_active_of_disjoint_closed_carriers hclosed hdisjoint hzero hxi

example {ι X A : Type*} [Fintype ι] [AddCommMonoid A] [TopologicalSpace X]
    {K : ι → Set X} {f : ι → X → A}
    (hclosed : ∀ i, IsClosed (K i))
    (hzero : ∀ i x, x ∉ K i → f i x = 0)
    {x : X} (hx : ∀ i, x ∉ K i) :
    (fun y => ∑ i, f i y) =ᶠ[𝓝 x] (fun _ => 0) :=
  finite_sum_eventuallyEq_zero_of_outside_closed_carriers hclosed hzero hx

example {ι X A : Type*} [Fintype ι] [AddCommMonoid A] [TopologicalSpace X]
    {K : ι → Set X} {f : ι → X → A}
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hzero : ∀ i x, x ∉ K i → f i x = 0) (x : X) :
    (∃ i, x ∈ K i ∧ (fun y => ∑ j, f j y) =ᶠ[𝓝 x] f i) ∨
      (fun y => ∑ j, f j y) =ᶠ[𝓝 x] (fun _ => 0) :=
  finite_sum_locally_active_or_zero hclosed hdisjoint hzero x

example {ι T X A : Type*} [Fintype ι] [TopologicalSpace T]
    [TopologicalSpace X] [AddCommMonoid A]
    {K : ι → Set X} {f : ι → T → X → A}
    (hclosed : ∀ i, IsClosed (K i))
    (hdisjoint : Pairwise fun i j => Disjoint (K i) (K j))
    (hzero : ∀ i t x, x ∉ K i → f i t x = 0)
    {i : ι} {x : X} (hxi : x ∈ K i) (t : T) :
    (fun z : T × X => ∑ j, f j z.1 z.2) =ᶠ[𝓝 (t, x)]
      (fun z => f i z.1 z.2) :=
  finite_sum_spacetime_eventuallyEq_active hclosed hdisjoint hzero hxi t

example {ι T X A : Type*} [Fintype ι] [TopologicalSpace T]
    [TopologicalSpace X] [AddCommMonoid A]
    {K : ι → Set X} {f : ι → T → X → A}
    (hclosed : ∀ i, IsClosed (K i))
    (hzero : ∀ i t x, x ∉ K i → f i t x = 0)
    {x : X} (hx : ∀ i, x ∉ K i) (t : T) :
    (fun z : T × X => ∑ j, f j z.1 z.2) =ᶠ[𝓝 (t, x)] (fun _ => 0) :=
  finite_sum_spacetime_eventuallyEq_zero hclosed hzero hx t

end Carriers

section PeriodicContracts

-- Literal equation, support, smoothness and quantifier semantics.
example (a b : Vec) : SameTorusPoint a b ↔
    ∃ k : Fin 3 → ℤ, ∀ i : Fin 3, b i = a i + (k i : ℝ) := Iff.rfl

example {N : ℕ} (a : Fin N → Vec) : TorusSitesDistinct a ↔
    ∀ i j : Fin N, SameTorusPoint (a i) (a j) → i = j := Iff.rfl

example : familySpacetime = {z : ℝ × Vec | z.1 ∈ Ico (0 : ℝ) 1} := rfl

example (F : Velocity) : AdmissiblePeriodicForce F ↔
    (ContDiff ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) ∧
      (∀ t : ℝ, SpatialPeriodic (F t)) ∧
      ∃ s r : ℝ, 0 < s ∧ s < r ∧ ∀ t : ℝ, t ∉ Icc s r → F t = 0) := by
  constructor
  · intro h
    exact ⟨h.smooth, h.periodic, h.time_support⟩
  · rintro ⟨hs, hp, ht⟩
    exact ⟨hs, hp, ht⟩

example (ν : ℝ) (F u : Velocity) (p : Pressure) :
    GlobalPeriodicCompetitor ν F u p ↔
      (ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) forwardSpacetime ∧
       ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) forwardSpacetime ∧
       (∀ t : ℝ, 0 ≤ t → SpatialPeriodic (u t)) ∧
       (∀ t : ℝ, 0 ≤ t → SpatialPeriodic (p t)) ∧
       (∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (u t) x = 0) ∧
       (∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
         timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
           ν • laplacian (u t) x + F t x) ∧ u 0 = 0) := by
  constructor
  · intro h
    exact ⟨h.velocity_smooth, h.pressure_smooth, h.velocity_periodic,
      h.pressure_periodic, h.divergence_free, h.equation, h.initial⟩
  · rintro ⟨hu, hp, hpu, hpp, hd, he, hi⟩
    exact ⟨hu, hp, hpu, hpp, hd, he, hi⟩

example (ν : ℝ) (F u : Velocity) (p : Pressure) :
    PreterminalPeriodicNSE ν F u p ↔
      (ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) familySpacetime ∧
       ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) familySpacetime ∧
       (∀ t ∈ Ico (0 : ℝ) 1, SpatialPeriodic (u t)) ∧
       (∀ t ∈ Ico (0 : ℝ) 1, SpatialPeriodic (p t)) ∧
       (∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Vec, divergence (u t) x = 0) ∧
       (∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Vec,
         timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
           ν • laplacian (u t) x + F t x) ∧ u 0 = 0) := by
  constructor
  · intro h
    exact ⟨h.velocity_smooth, h.pressure_smooth, h.velocity_periodic,
      h.pressure_periodic, h.divergence_free, h.equation, h.initial⟩
  · rintro ⟨hu, hp, hpu, hpp, hd, he, hi⟩
    exact ⟨hu, hp, hpu, hpp, hd, he, hi⟩

example (u : Velocity) : BoundedPreterminalCellEnergy u ↔
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Ico (0 : ℝ) 1,
      IntegrableOn (fun x => ‖u t x‖ ^ 2) unitCube volume ∧
        (∫ x in unitCube, ‖u t x‖ ^ 2) ≤ E := Iff.rfl

example {N : ℕ} (ν : ℝ) (a : Fin N → Vec) (F u : Velocity) (p : Pressure) :
    PeriodicFamilyWitness ν a F u p ↔
      (AdmissiblePeriodicForce F ∧ PreterminalPeriodicNSE ν F u p ∧
       BoundedPreterminalCellEnergy u ∧
       (∀ i : Fin N, LocalVelocityBlowup u (a i) 1) ∧
       ¬ ∃ (v : Velocity) (q : Pressure), GlobalPeriodicCompetitor ν F v q) := by
  constructor
  · intro h
    exact ⟨h.force, h.front, h.energy, h.local_blowup, h.no_global⟩
  · rintro ⟨hf, hn, he, hb, hg⟩
    exact ⟨hf, hn, he, hb, hg⟩

example : PeriodicFamilyObstructionStatement ↔
    ∀ ν : ℝ, 0 < ν → ∀ N : ℕ, 0 < N → ∀ a : Fin N → Vec,
      TorusSitesDistinct a →
        ∃ (F u : Velocity) (p : Pressure), PeriodicFamilyWitness ν a F u p := Iff.rfl

example (ν : ℝ) : SmoothCompactForceObstruction ν ↔
    ∃ F : Velocity, AdmissiblePeriodicForce F ∧
      ¬ ∃ (v : Velocity) (q : Pressure), GlobalPeriodicCompetitor ν F v q := Iff.rfl

-- Full helper signatures; none constructs a periodic singular family.
example (a : Vec) : SameTorusPoint a a := sameTorusPoint_refl a

example {a b : Vec} (h : SameTorusPoint a b) : SameTorusPoint b a :=
  sameTorusPoint_symm h

example {a b c : Vec} (hab : SameTorusPoint a b) (hbc : SameTorusPoint b c) :
    SameTorusPoint a c := sameTorusPoint_trans hab hbc

example {N : ℕ} {a : Fin N → Vec} (h : TorusSitesDistinct a) :
    Function.Injective a := torusSitesDistinct_injective h

example (a : Fin 1 → Vec) : TorusSitesDistinct a := torusSitesDistinct_singleton a

example {M N : ℕ} {a : Fin N → Vec} (h : TorusSitesDistinct a)
    (e : Fin M → Fin N) (he : Function.Injective e) :
    TorusSitesDistinct (a ∘ e) := torusSitesDistinct_reindex h e he

example : AdmissiblePeriodicForce (0 : Velocity) := admissiblePeriodicForce_zero

example {ν : ℝ} {u : Velocity} {p : Pressure}
    (h : GlobalSmoothNSE ν (0 : Field) u p) :
    GlobalPeriodicCompetitor ν (0 : Velocity) u p :=
  globalPeriodicCompetitor_of_unforced h

example (ν : ℝ) :
    GlobalPeriodicCompetitor ν (0 : Velocity) (0 : Velocity) (0 : Pressure) :=
  globalPeriodicCompetitor_zero ν

example {ν : ℝ} {F u : Velocity} {p : Pressure}
    (h : GlobalPeriodicCompetitor ν F u p) : PreterminalPeriodicNSE ν F u p :=
  preterminalPeriodicNSE_of_global h

example {M N : ℕ} {ν : ℝ} {a : Fin N → Vec} {F u : Velocity} {p : Pressure}
    (h : PeriodicFamilyWitness ν a F u p) (e : Fin M → Fin N) :
    PeriodicFamilyWitness ν (a ∘ e) F u p := periodicFamilyWitness_reindex h e

example {N : ℕ} (ν : ℝ) (a : Fin N → Vec) (u : Velocity) (p : Pressure) :
    ¬ PeriodicFamilyWitness ν a (0 : Velocity) u p :=
  no_periodicFamilyWitness_zero_force ν a u p

example (h : PeriodicFamilyObstructionStatement) (ν : ℝ) (hν : 0 < ν) :
    SmoothCompactForceObstruction ν := family_implies_smoothCompactForceObstruction h ν hν

end PeriodicContracts

end FeffermanFamilyFoundation.TypeChecks

-- BEGIN COMPLETE ORDERED TYPE/AXIOM REPORTS

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.terminal_pos"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.terminal_pos
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.terminal_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.terminal_pos"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.terminal_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.terminal_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.congr_on_left"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.congr_on_left
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.congr_on_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.congr_on_left"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.congr_on_left
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.congr_on_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_locally_bounded"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_locally_bounded
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_locally_bounded"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_locally_bounded"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_locally_bounded
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_locally_bounded"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt_of_agrees"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt_of_agrees
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt_of_agrees"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt_of_agrees"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt_of_agrees
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.not_continuousAt_of_agrees"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.of_sequence"
#check @MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.of_sequence
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.of_sequence"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.of_sequence"
#print axioms MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.of_sequence
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.LocalVelocityBlowup.of_sequence"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.exists_localVelocityBlowup_of_compact_sequence"
#check @MethbokeAddon.FeffermanFamily.exists_localVelocityBlowup_of_compact_sequence
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.exists_localVelocityBlowup_of_compact_sequence"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.exists_localVelocityBlowup_of_compact_sequence"
#print axioms MethbokeAddon.FeffermanFamily.exists_localVelocityBlowup_of_compact_sequence
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.exists_localVelocityBlowup_of_compact_sequence"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.supported_eventuallyEq_zero_of_not_mem"
#check @MethbokeAddon.FeffermanFamily.supported_eventuallyEq_zero_of_not_mem
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.supported_eventuallyEq_zero_of_not_mem"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.supported_eventuallyEq_zero_of_not_mem"
#print axioms MethbokeAddon.FeffermanFamily.supported_eventuallyEq_zero_of_not_mem
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.supported_eventuallyEq_zero_of_not_mem"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_eq_active_of_disjoint_carriers"
#check @MethbokeAddon.FeffermanFamily.finite_sum_eq_active_of_disjoint_carriers
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.finite_sum_eq_active_of_disjoint_carriers"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_eq_active_of_disjoint_carriers"
#print axioms MethbokeAddon.FeffermanFamily.finite_sum_eq_active_of_disjoint_carriers
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.finite_sum_eq_active_of_disjoint_carriers"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_eq_zero_of_outside_carriers"
#check @MethbokeAddon.FeffermanFamily.finite_sum_eq_zero_of_outside_carriers
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.finite_sum_eq_zero_of_outside_carriers"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_eq_zero_of_outside_carriers"
#print axioms MethbokeAddon.FeffermanFamily.finite_sum_eq_zero_of_outside_carriers
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.finite_sum_eq_zero_of_outside_carriers"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_active_of_disjoint_closed_carriers"
#check @MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_active_of_disjoint_closed_carriers
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_active_of_disjoint_closed_carriers"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_active_of_disjoint_closed_carriers"
#print axioms MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_active_of_disjoint_closed_carriers
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_active_of_disjoint_closed_carriers"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_zero_of_outside_closed_carriers"
#check @MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_zero_of_outside_closed_carriers
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_zero_of_outside_closed_carriers"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_zero_of_outside_closed_carriers"
#print axioms MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_zero_of_outside_closed_carriers
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.finite_sum_eventuallyEq_zero_of_outside_closed_carriers"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_locally_active_or_zero"
#check @MethbokeAddon.FeffermanFamily.finite_sum_locally_active_or_zero
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.finite_sum_locally_active_or_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_locally_active_or_zero"
#print axioms MethbokeAddon.FeffermanFamily.finite_sum_locally_active_or_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.finite_sum_locally_active_or_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_active"
#check @MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_active
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_active"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_active"
#print axioms MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_active
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_active"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_zero"
#check @MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_zero
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_zero"
#print axioms MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.finite_sum_spacetime_eventuallyEq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.SameTorusPoint"
#check @MethbokeAddon.FeffermanFamily.SameTorusPoint
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.SameTorusPoint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.SameTorusPoint"
#print axioms MethbokeAddon.FeffermanFamily.SameTorusPoint
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.SameTorusPoint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.TorusSitesDistinct"
#check @MethbokeAddon.FeffermanFamily.TorusSitesDistinct
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.TorusSitesDistinct"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.TorusSitesDistinct"
#print axioms MethbokeAddon.FeffermanFamily.TorusSitesDistinct
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.TorusSitesDistinct"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.familySpacetime"
#check @MethbokeAddon.FeffermanFamily.familySpacetime
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.familySpacetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.familySpacetime"
#print axioms MethbokeAddon.FeffermanFamily.familySpacetime
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.familySpacetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce"
#check @MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce"
#print axioms MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.GlobalPeriodicCompetitor"
#check @MethbokeAddon.FeffermanFamily.GlobalPeriodicCompetitor
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.GlobalPeriodicCompetitor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.GlobalPeriodicCompetitor"
#print axioms MethbokeAddon.FeffermanFamily.GlobalPeriodicCompetitor
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.GlobalPeriodicCompetitor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.PreterminalPeriodicNSE"
#check @MethbokeAddon.FeffermanFamily.PreterminalPeriodicNSE
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.PreterminalPeriodicNSE"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.PreterminalPeriodicNSE"
#print axioms MethbokeAddon.FeffermanFamily.PreterminalPeriodicNSE
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.PreterminalPeriodicNSE"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.BoundedPreterminalCellEnergy"
#check @MethbokeAddon.FeffermanFamily.BoundedPreterminalCellEnergy
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.BoundedPreterminalCellEnergy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.BoundedPreterminalCellEnergy"
#print axioms MethbokeAddon.FeffermanFamily.BoundedPreterminalCellEnergy
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.BoundedPreterminalCellEnergy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.PeriodicFamilyWitness"
#check @MethbokeAddon.FeffermanFamily.PeriodicFamilyWitness
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.PeriodicFamilyWitness"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.PeriodicFamilyWitness"
#print axioms MethbokeAddon.FeffermanFamily.PeriodicFamilyWitness
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.PeriodicFamilyWitness"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.PeriodicFamilyObstructionStatement"
#check @MethbokeAddon.FeffermanFamily.PeriodicFamilyObstructionStatement
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.PeriodicFamilyObstructionStatement"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.PeriodicFamilyObstructionStatement"
#print axioms MethbokeAddon.FeffermanFamily.PeriodicFamilyObstructionStatement
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.PeriodicFamilyObstructionStatement"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.SmoothCompactForceObstruction"
#check @MethbokeAddon.FeffermanFamily.SmoothCompactForceObstruction
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.SmoothCompactForceObstruction"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.SmoothCompactForceObstruction"
#print axioms MethbokeAddon.FeffermanFamily.SmoothCompactForceObstruction
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.SmoothCompactForceObstruction"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.sameTorusPoint_refl"
#check @MethbokeAddon.FeffermanFamily.sameTorusPoint_refl
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.sameTorusPoint_refl"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.sameTorusPoint_refl"
#print axioms MethbokeAddon.FeffermanFamily.sameTorusPoint_refl
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.sameTorusPoint_refl"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.sameTorusPoint_symm"
#check @MethbokeAddon.FeffermanFamily.sameTorusPoint_symm
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.sameTorusPoint_symm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.sameTorusPoint_symm"
#print axioms MethbokeAddon.FeffermanFamily.sameTorusPoint_symm
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.sameTorusPoint_symm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.sameTorusPoint_trans"
#check @MethbokeAddon.FeffermanFamily.sameTorusPoint_trans
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.sameTorusPoint_trans"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.sameTorusPoint_trans"
#print axioms MethbokeAddon.FeffermanFamily.sameTorusPoint_trans
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.sameTorusPoint_trans"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.torusSitesDistinct_injective"
#check @MethbokeAddon.FeffermanFamily.torusSitesDistinct_injective
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.torusSitesDistinct_injective"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.torusSitesDistinct_injective"
#print axioms MethbokeAddon.FeffermanFamily.torusSitesDistinct_injective
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.torusSitesDistinct_injective"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.torusSitesDistinct_singleton"
#check @MethbokeAddon.FeffermanFamily.torusSitesDistinct_singleton
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.torusSitesDistinct_singleton"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.torusSitesDistinct_singleton"
#print axioms MethbokeAddon.FeffermanFamily.torusSitesDistinct_singleton
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.torusSitesDistinct_singleton"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.torusSitesDistinct_reindex"
#check @MethbokeAddon.FeffermanFamily.torusSitesDistinct_reindex
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.torusSitesDistinct_reindex"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.torusSitesDistinct_reindex"
#print axioms MethbokeAddon.FeffermanFamily.torusSitesDistinct_reindex
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.torusSitesDistinct_reindex"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.admissiblePeriodicForce_zero"
#check @MethbokeAddon.FeffermanFamily.admissiblePeriodicForce_zero
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.admissiblePeriodicForce_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.admissiblePeriodicForce_zero"
#print axioms MethbokeAddon.FeffermanFamily.admissiblePeriodicForce_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.admissiblePeriodicForce_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_of_unforced"
#check @MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_of_unforced
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_of_unforced"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_of_unforced"
#print axioms MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_of_unforced
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_of_unforced"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_zero"
#check @MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_zero
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_zero"
#print axioms MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.globalPeriodicCompetitor_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.preterminalPeriodicNSE_of_global"
#check @MethbokeAddon.FeffermanFamily.preterminalPeriodicNSE_of_global
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.preterminalPeriodicNSE_of_global"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.preterminalPeriodicNSE_of_global"
#print axioms MethbokeAddon.FeffermanFamily.preterminalPeriodicNSE_of_global
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.preterminalPeriodicNSE_of_global"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.periodicFamilyWitness_reindex"
#check @MethbokeAddon.FeffermanFamily.periodicFamilyWitness_reindex
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.periodicFamilyWitness_reindex"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.periodicFamilyWitness_reindex"
#print axioms MethbokeAddon.FeffermanFamily.periodicFamilyWitness_reindex
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.periodicFamilyWitness_reindex"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.no_periodicFamilyWitness_zero_force"
#check @MethbokeAddon.FeffermanFamily.no_periodicFamilyWitness_zero_force
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.no_periodicFamilyWitness_zero_force"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.no_periodicFamilyWitness_zero_force"
#print axioms MethbokeAddon.FeffermanFamily.no_periodicFamilyWitness_zero_force
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.no_periodicFamilyWitness_zero_force"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FeffermanFamily.family_implies_smoothCompactForceObstruction"
#check @MethbokeAddon.FeffermanFamily.family_implies_smoothCompactForceObstruction
#eval IO.println "TYPE_END:MethbokeAddon.FeffermanFamily.family_implies_smoothCompactForceObstruction"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FeffermanFamily.family_implies_smoothCompactForceObstruction"
#print axioms MethbokeAddon.FeffermanFamily.family_implies_smoothCompactForceObstruction
#eval IO.println "AXIOMS_END:MethbokeAddon.FeffermanFamily.family_implies_smoothCompactForceObstruction"
