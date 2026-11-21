import MethbokeAddon.QuasiFeffermanA.Contracts
import SingularClosure.Contracts

/-!
# Literal whole-space NSE-A target

The datum is an actual real Schwartz field on Euclidean three-space. The
solution predicate uses the actual unforced differential equation on the
closed nonnegative-time domain, its exact initial value, and a uniform
whole-space energy bound with explicit integrability.

Pressure has its unrestricted additive time gauge. No Sobolev regularity,
projected equation, regularized flow, stability estimate, or stopped drift
inequality is a field of this contract. Those analytical admission steps
must be proved separately before an R3 obstruction can be inferred.

Defining `NSE_A` does not establish or refute it. The zero witness below only
checks that the literal contract admits its expected elementary solution.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace MethbokeAddon.R3Ehrenfest

open QuasiFeffermanA

/-- Real, divergence-free Schwartz initial data on the full spatial domain. -/
structure SmoothDatum where
  value : SchwartzMap Space Space
  divergence_free : ∀ x : Space, SingularClosure.divergence value x = 0

/-- A uniform full-space kinetic-energy bound, with genuine integrability. -/
def UniformFiniteEnergy (u : SingularClosure.Velocity) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, 0 ≤ t →
    Integrable (fun x : Space => ‖u t x‖ ^ 2) volume ∧
      (∫ x : Space, ‖u t x‖ ^ 2) ≤ E

/-- Literal global smooth unforced NSE on R3, with no pressure normalization. -/
structure GlobalSmoothNSE (ν : ℝ) (a : SmoothDatum)
    (u : SingularClosure.Velocity) (p : SingularClosure.Pressure) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × Space => u z.1 z.2) SingularClosure.forwardSpacetime
  pressure_smooth : ContDiffOn ℝ ∞
    (fun z : ℝ × Space => p z.1 z.2) SingularClosure.forwardSpacetime
  divergence_free : ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
    SingularClosure.divergence (u t) x = 0
  equation : ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
    SingularClosure.timeDerivative u t x + SingularClosure.convection (u t) x +
      SingularClosure.gradient (p t) x = ν • SingularClosure.laplacian (u t) x
  initial : u 0 = a.value
  finite_energy : UniformFiniteEnergy u

/-- The all-Schwartz-data existence statement at the specified viscosity. -/
def NSE_A (ν : ℝ) : Prop :=
  ∀ a : SmoothDatum, ∃ (u : SingularClosure.Velocity) (p : SingularClosure.Pressure),
    GlobalSmoothNSE ν a u p

/-- The zero Schwartz field belongs to the literal datum category. -/
def zeroDatum : SmoothDatum where
  value := 0
  divergence_free := by
    intro x
    simpa using (SingularClosure.smoothSigmaZero_zero.divergence_free x)

/-- The genuine zero solution satisfies the whole-space finite-energy bound. -/
theorem uniformFiniteEnergy_zero : UniformFiniteEnergy (0 : SingularClosure.Velocity) := by
  refine ⟨0, le_rfl, ?_⟩
  intro t ht
  constructor <;> simp

/-- A concrete consistency witness for the literal R3 solution category. -/
theorem globalSmoothNSE_zero (ν : ℝ) :
    GlobalSmoothNSE ν zeroDatum (0 : SingularClosure.Velocity)
      (0 : SingularClosure.Pressure) := by
  have h := SingularClosure.globalSmoothNSE_zero ν
  exact ⟨h.velocity_smooth, h.pressure_smooth, h.divergence_free, h.equation,
    by rfl, uniformFiniteEnergy_zero⟩

/-- One actual unsolvable datum would refute this exact literal target.
The premise is an explicit counterexample, not a constructed one. -/
theorem not_NSE_A_of_counterexample {ν : ℝ} (a : SmoothDatum)
    (ha : ∀ (u : SingularClosure.Velocity) (p : SingularClosure.Pressure),
      ¬ GlobalSmoothNSE ν a u p) : ¬ NSE_A ν := by
  intro h
  obtain ⟨u, p, hp⟩ := h a
  exact ha u p hp

end MethbokeAddon.R3Ehrenfest
