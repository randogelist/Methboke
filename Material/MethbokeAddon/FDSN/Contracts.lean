import MethbokeAddon.FeffermanFamily.FamilyContracts

/-!
# Faithful periodic FDSN seed and basic admission transport

The spatial torus is represented by unit-periodic functions on the native
Euclidean `Vec`.  Time and initial datum are unrestricted: no normalization
to terminal time one or zero initial velocity is made.

`Seed` is a hypothesis contract only. It contains no phase family, no fixed
forcing nonuniqueness premise and no terminal derivative-growth hypothesis.
The family conclusion will be assembled after its concrete helical and
smooth-seminorm APIs are fixed.

Prepared by static inspection for the authorized external CI; never run locally.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

open SingularClosure

noncomputable section

def preterminalSpacetime (T : ℝ) : Set (ℝ × Vec) :=
  {z | z.1 ∈ Ico (0 : ℝ) T}

/-- The actual forced PDE and its regularity on an arbitrary preterminal slab. -/
structure PreterminalNSE (ν T : ℝ) (u : Velocity) (p : Pressure)
    (F : Velocity) : Prop where
  velocity_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (preterminalSpacetime T)
  pressure_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) (preterminalSpacetime T)
  velocity_periodic : ∀ t ∈ Ico (0 : ℝ) T, SpatialPeriodic (u t)
  pressure_periodic : ∀ t ∈ Ico (0 : ℝ) T, SpatialPeriodic (p t)
  divergence_free : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
      ν • laplacian (u t) x + F t x

/-- Uniform preterminal kinetic energy with explicit physical integrability. -/
def BoundedCellEnergy (T : ℝ) (u : Velocity) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Ico (0 : ℝ) T,
    IntegrableOn (fun x => ‖u t x‖ ^ 2) unitCube volume ∧
      (∫ x in unitCube, ‖u t x‖ ^ 2) ≤ E

/-- Squared spatial gradient, expressed through the actual native coordinate
derivatives, with no mean-zero hypothesis. -/
def gradientSquare (v : Field) (x : Vec) : ℝ :=
  ∑ i : Fin 3, ‖coordinateDerivative v i x‖ ^ 2

def cellDissipation (v : Field) : ℝ :=
  ∫ x in unitCube, gradientSquare v x

/-- Finite physical integrated dissipation. Integrability is explicit both
for each spatial integral and for the preterminal time integral. -/
def FiniteDissipation (T : ℝ) (u : Velocity) : Prop :=
  (∀ t ∈ Ico (0 : ℝ) T, IntegrableOn (gradientSquare (u t)) unitCube volume) ∧
    IntegrableOn (fun t => cellDissipation (u t)) (Ioo (0 : ℝ) T) volume

/-- Cofinal unboundedness of the physical velocity near the terminal time.
For a continuous periodic field this is the literal pointwise-witness form
of `limsup_(t up T) ||u(t)||_infinity = infinity`, avoiding a totalized supremum.
Its equivalence to any later packaged sup-norm API is a separate adapter. -/
def CofinalVelocityBlowup (T : ℝ) (u : Velocity) : Prop :=
  ∀ s ∈ Ico (0 : ℝ) T, ∀ M : ℝ, 0 ≤ M →
    ∃ t ∈ Ioo s T, ∃ x ∈ unitCube, M < ‖u t x‖

/-- Canonical FDSN input on the unit three-torus.  Initial velocity is `u 0`
and may have arbitrary spatial mean. -/
structure Seed (ν T : ℝ) (u : Velocity) (p : Pressure)
    (F : Velocity) : Prop where
  viscosity_pos : 0 < ν
  terminal_pos : 0 < T
  front : PreterminalNSE ν T u p F
  force : MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce F
  initial_smooth : ContDiff ℝ ∞ (u 0)
  bounded_energy : BoundedCellEnergy T u
  finite_dissipation : FiniteDissipation T u
  terminal_blowup : CofinalVelocityBlowup T u

theorem Seed.initial_periodic {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) : SpatialPeriodic (u 0) :=
  h.front.velocity_periodic 0 ⟨le_rfl, h.terminal_pos⟩

theorem Seed.initial_divergence_free {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) : ∀ x : Vec, divergence (u 0) x = 0 :=
  h.front.divergence_free 0 ⟨le_rfl, h.terminal_pos⟩

theorem gradientSquare_nonneg (v : Field) (x : Vec) :
    0 ≤ gradientSquare v x := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

/-- Exact agreement on a final interval transports the same terminal blowup. -/
theorem cofinalVelocityBlowup_of_late_eq {T r : ℝ} {u v : Velocity}
    (hr : r < T) (hu : CofinalVelocityBlowup T u)
    (heq : ∀ t ∈ Ioo r T, v t = u t) : CofinalVelocityBlowup T v := by
  intro s hs M hM
  have hmax : max s r ∈ Ico (0 : ℝ) T :=
    ⟨le_trans hs.1 (le_max_left s r), max_lt_iff.mpr ⟨hs.2, hr⟩⟩
  obtain ⟨t, ht, x, hx, hlarge⟩ := hu (max s r) hmax M hM
  have hst : s < t := lt_of_le_of_lt (le_max_left s r) ht.1
  have hrt : r < t := lt_of_le_of_lt (le_max_right s r) ht.1
  refine ⟨t, ⟨hst, ht.2⟩, x, hx, ?_⟩
  rw [heq t ⟨hrt, ht.2⟩]
  exact hlarge

/-- Smooth compact positive-time forcing is closed under addition. -/
theorem admissiblePeriodicForce_add {F G : Velocity}
    (hF : MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce F)
    (hG : MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce G) :
    MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce (F + G) := by
  refine ⟨hF.smooth.add hG.smooth, ?_, ?_⟩
  · intro t x i
    change F t (x + unitVector i) + G t (x + unitVector i) = F t x + G t x
    rw [hF.periodic t x i, hG.periodic t x i]
  · obtain ⟨a, b, ha, hab, hFs⟩ := hF.time_support
    obtain ⟨c, d, hc, hcd, hGs⟩ := hG.time_support
    refine ⟨min a c, max b d, lt_min_iff.mpr ⟨ha, hc⟩, ?_, ?_⟩
    · exact lt_of_le_of_lt (min_le_left a c)
        (lt_of_lt_of_le hab (le_max_left b d))
    · intro t ht
      have htF : t ∉ Icc a b := by
        intro h
        exact ht ⟨le_trans (min_le_left a c) h.1,
          le_trans h.2 (le_max_left b d)⟩
      have htG : t ∉ Icc c d := by
        intro h
        exact ht ⟨le_trans (min_le_right a c) h.1,
          le_trans h.2 (le_max_right b d)⟩
      change F t + G t = 0
      rw [hFs t htF, hGs t htG, zero_add]

end

end MethbokeAddon.FDSN
