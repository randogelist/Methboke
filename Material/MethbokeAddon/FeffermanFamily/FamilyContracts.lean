import SingularClosure.Contracts
import MethbokeAddon.FeffermanFamily.LocalBlowup

/-!
# Concrete periodic contracts for the finite-site forced family

The domain is the unit three-torus, represented by the native unit-periodic
lifts on `SingularClosure.Vec`. Distinct sites mean distinct modulo the
integer lattice, not merely distinct representatives in Euclidean space.

Every differential operator below is the existing physical operator from
`SingularClosure.Contracts`. Smoothness is `ContDiff` order `∞`, not analytic
order `ω`. The force is the same prescribed function in the constructed
front and every excluded global competitor. Both velocity and pressure must
be periodic. A competitor has no extra energy, mean-zero or pressure-gauge
condition. The squared-norm integral in the witness has explicit integrability.

`PeriodicFamilyObstructionStatement` specifies the eventual theorem named
`Fefferman_D_Family_obstruction`. This file does not assert that theorem or
import a seed by an axiom. The helper implication only forgets information
from an explicitly supplied family theorem.

Prepared for matching cached external compilation and exact-type/axiom audit.
No local Lean execution.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped ContDiff

namespace MethbokeAddon.FeffermanFamily

noncomputable section

/-- Equality of represented points of `R^3 / Z^3`, in coordinates. -/
def SameTorusPoint (a b : Vec) : Prop :=
  ∃ k : Fin 3 → ℤ, ∀ i : Fin 3, b i = a i + (k i : ℝ)

theorem sameTorusPoint_refl (a : Vec) : SameTorusPoint a a := by
  refine ⟨fun _ => 0, ?_⟩
  intro i
  simp

theorem sameTorusPoint_symm {a b : Vec} (h : SameTorusPoint a b) :
    SameTorusPoint b a := by
  obtain ⟨k, hk⟩ := h
  refine ⟨fun i => -k i, ?_⟩
  intro i
  rw [Int.cast_neg, hk i]
  ring

theorem sameTorusPoint_trans {a b c : Vec}
    (hab : SameTorusPoint a b) (hbc : SameTorusPoint b c) :
    SameTorusPoint a c := by
  obtain ⟨k, hk⟩ := hab
  obtain ⟨l, hl⟩ := hbc
  refine ⟨fun i => k i + l i, ?_⟩
  intro i
  rw [Int.cast_add, hl i, hk i]
  ring

/-- A finite tuple has distinct torus sites, independently of lift choices. -/
def TorusSitesDistinct {N : ℕ} (a : Fin N → Vec) : Prop :=
  ∀ i j : Fin N, SameTorusPoint (a i) (a j) → i = j

theorem torusSitesDistinct_injective {N : ℕ} {a : Fin N → Vec}
    (h : TorusSitesDistinct a) : Function.Injective a := by
  intro i j hij
  apply h i j
  rw [hij]
  exact sameTorusPoint_refl (a j)

theorem torusSitesDistinct_singleton (a : Fin 1 → Vec) :
    TorusSitesDistinct a := by
  intro i j _
  exact Subsingleton.elim i j

theorem torusSitesDistinct_reindex {M N : ℕ} {a : Fin N → Vec}
    (h : TorusSitesDistinct a) (e : Fin M → Fin N)
    (he : Function.Injective e) : TorusSitesDistinct (a ∘ e) := by
  intro i j hij
  exact he (h (e i) (e j) hij)

/-- The preterminal domain includes the initial-time boundary, but not time one. -/
def familySpacetime : Set (ℝ × Vec) :=
  {z | z.1 ∈ Ico (0 : ℝ) 1}

/-- Globally smooth periodic force, supported in a compact positive-time slab.
The force is prescribed for all times, including at and beyond the blowup time.
-/
structure AdmissiblePeriodicForce (F : Velocity) : Prop where
  smooth : ContDiff ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2)
  periodic : ∀ t : ℝ, SpatialPeriodic (F t)
  time_support : ∃ s r : ℝ, 0 < s ∧ s < r ∧
    ∀ t : ℝ, t ∉ Icc s r → F t = 0

/-- An actual global smooth forced solution with zero datum. No extra energy
bound, zero-mean condition or pressure normalization is imposed.
-/
structure GlobalPeriodicCompetitor (ν : ℝ) (F u : Velocity) (p : Pressure) : Prop where
  velocity_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) forwardSpacetime
  pressure_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) forwardSpacetime
  velocity_periodic : ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (u t)
  pressure_periodic : ∀ t : ℝ, 0 ≤ t → SpatialPeriodic (p t)
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t : ℝ, 0 ≤ t → ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
      ν • laplacian (u t) x + F t x
  initial : u 0 = 0

/-- The same physical forced PDE, required only on the preterminal domain. -/
structure PreterminalPeriodicNSE (ν : ℝ) (F u : Velocity) (p : Pressure) : Prop where
  velocity_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) familySpacetime
  pressure_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) familySpacetime
  velocity_periodic : ∀ t ∈ Ico (0 : ℝ) 1, SpatialPeriodic (u t)
  pressure_periodic : ∀ t ∈ Ico (0 : ℝ) 1, SpatialPeriodic (p t)
  divergence_free : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t ∈ Ico (0 : ℝ) 1, ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
      ν • laplacian (u t) x + F t x
  initial : u 0 = 0

/-- Uniformly finite squared physical `L2` norm before time one. Explicit
integrability excludes the default value of a nonintegrable Bochner integral.
-/
def BoundedPreterminalCellEnergy (u : Velocity) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Ico (0 : ℝ) 1,
    IntegrableOn (fun x => ‖u t x‖ ^ 2) unitCube volume ∧
      (∫ x in unitCube, ‖u t x‖ ^ 2) ≤ E

/-- All fields belong to the same witness. This is a target contract, not a
construction of one. Sites need not exhaust the full singular set.
-/
structure PeriodicFamilyWitness {N : ℕ} (ν : ℝ) (a : Fin N → Vec)
    (F u : Velocity) (p : Pressure) : Prop where
  force : AdmissiblePeriodicForce F
  front : PreterminalPeriodicNSE ν F u p
  energy : BoundedPreterminalCellEnergy u
  local_blowup : ∀ i : Fin N, LocalVelocityBlowup u (a i) 1
  no_global : ¬ ∃ (v : Velocity) (q : Pressure), GlobalPeriodicCompetitor ν F v q

/-- Exact target for the future `Fefferman_D_Family_obstruction` theorem.
Quantification over arbitrary lifted tuples with distinct torus classes is
the native periodic-lift presentation of finite distinct sites on the torus.
The force may depend on the configuration. No witness is assumed globally.
-/
def PeriodicFamilyObstructionStatement : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ N : ℕ, 0 < N → ∀ a : Fin N → Vec,
    TorusSitesDistinct a →
      ∃ (F u : Velocity) (p : Pressure), PeriodicFamilyWitness ν a F u p

/-- The single-force obstruction obtained by forgetting all site and energy
information. The admissible force class is a smooth compact-time subclass.
-/
def SmoothCompactForceObstruction (ν : ℝ) : Prop :=
  ∃ F : Velocity, AdmissiblePeriodicForce F ∧
    ¬ ∃ (v : Velocity) (q : Pressure), GlobalPeriodicCompetitor ν F v q

theorem admissiblePeriodicForce_zero : AdmissiblePeriodicForce (0 : Velocity) := by
  refine ⟨contDiff_const, ?_, ?_⟩
  · intro t x i
    rfl
  · refine ⟨1, 2, by norm_num, by norm_num, ?_⟩
    intro t _
    rfl

/-- Existing unforced solutions are admitted when the prescribed force is zero.
Dropping their normalization fields enlarges the competitor class.
-/
theorem globalPeriodicCompetitor_of_unforced {ν : ℝ} {u : Velocity} {p : Pressure}
    (h : GlobalSmoothNSE ν (0 : Field) u p) :
    GlobalPeriodicCompetitor ν (0 : Velocity) u p := by
  refine {
    velocity_smooth := h.velocity_smooth
    pressure_smooth := h.pressure_smooth
    velocity_periodic := h.velocity_periodic
    pressure_periodic := h.pressure_periodic
    divergence_free := h.divergence_free
    equation := ?_
    initial := h.initial
  }
  intro t ht x
  simpa only [Pi.zero_apply, add_zero] using h.equation t ht x

theorem globalPeriodicCompetitor_zero (ν : ℝ) :
    GlobalPeriodicCompetitor ν (0 : Velocity) (0 : Velocity) (0 : Pressure) :=
  globalPeriodicCompetitor_of_unforced (globalSmoothNSE_zero ν)

/-- Restriction uses the same force and fields; no solution existence is inferred. -/
theorem preterminalPeriodicNSE_of_global {ν : ℝ} {F u : Velocity} {p : Pressure}
    (h : GlobalPeriodicCompetitor ν F u p) : PreterminalPeriodicNSE ν F u p := by
  have hsub : familySpacetime ⊆ forwardSpacetime := by
    intro z hz
    exact hz.1
  exact {
    velocity_smooth := h.velocity_smooth.mono hsub
    pressure_smooth := h.pressure_smooth.mono hsub
    velocity_periodic := fun t ht => h.velocity_periodic t ht.1
    pressure_periodic := fun t ht => h.pressure_periodic t ht.1
    divergence_free := fun t ht => h.divergence_free t ht.1
    equation := fun t ht => h.equation t ht.1
    initial := h.initial
  }

/-- Selecting sites retains the very same force, front, energy and obstruction. -/
theorem periodicFamilyWitness_reindex {M N : ℕ} {ν : ℝ} {a : Fin N → Vec}
    {F u : Velocity} {p : Pressure} (h : PeriodicFamilyWitness ν a F u p)
    (e : Fin M → Fin N) : PeriodicFamilyWitness ν (a ∘ e) F u p := by
  exact {
    force := h.force
    front := h.front
    energy := h.energy
    local_blowup := fun i => h.local_blowup (e i)
    no_global := h.no_global
  }

/-- The zero force cannot satisfy this nonexistence contract: the native zero
solution is an admitted global competitor.
-/
theorem no_periodicFamilyWitness_zero_force {N : ℕ} (ν : ℝ) (a : Fin N → Vec)
    (u : Velocity) (p : Pressure) :
    ¬ PeriodicFamilyWitness ν a (0 : Velocity) u p := by
  intro h
  exact h.no_global ⟨0, 0, globalPeriodicCompetitor_zero ν⟩

/-- A proved finite-family statement would imply the one-force obstruction.
The premise remains explicit; this theorem does not construct the seed or family.
-/
theorem family_implies_smoothCompactForceObstruction
    (h : PeriodicFamilyObstructionStatement) (ν : ℝ) (hν : 0 < ν) :
    SmoothCompactForceObstruction ν := by
  obtain ⟨F, u, p, H⟩ := h ν hν 1 (by decide) (fun _ => 0)
    (torusSitesDistinct_singleton (fun _ => 0))
  exact ⟨F, H.force, H.no_global⟩

end

end MethbokeAddon.FeffermanFamily
