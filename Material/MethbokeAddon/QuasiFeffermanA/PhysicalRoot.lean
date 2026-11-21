import MethbokeAddon.QuasiFeffermanA.Contracts
import SingularClosure.Contracts

/-!
# Exact physical whole-space Quasi-Fefferman A conclusion

This file fixes the current root without assuming any of its analytic
conclusions. Data are arbitrary full-volume solenoidal L2 classes. Every
supplied Leray--Hopf path is retained, including its exact trace at each tail
start. Smooth velocity representatives agree spatially almost everywhere at
every tail time; future uniqueness concerns L2 velocities, not arbitrary
values of a weak-gradient witness on a time-null set.

Pressure is explicitly normalized by p(t, 0) = 0. This is a smooth time gauge,
not an L2 or Riesz-transform normalization; no pressure Lp claim is made.
The imported differential operators are the actual Euclidean derivatives.
No periodicity or mean-zero hypothesis from their source is imported here.

The strict-cutoff root and its stronger closed-cutoff version are separately
named. Defining either proposition is not a proof of general QFA.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff Interval

namespace MethbokeAddon.QuasiFeffermanA.PhysicalRoot

/-- The frozen whole-space QFA cutoff, with the exact sharp constant. -/
def cutoff (ν : ℝ) (a : SpatialL2) : ℝ :=
  8 * ‖a‖ ^ 4 / (27 * Real.pi ^ 4 * ν ^ 5)

/-- Closed tail spacetime, including the exact start. -/
def tailSpacetime (δ : ℝ) : Set (ℝ × Space) := {z | δ ≤ z.1}

/-- Actual classical unforced NSE on the full spatial domain and closed tail.
The pressure convention fixes only its additive time gauge. -/
structure ClassicalTail (ν δ : ℝ)
    (v : SingularClosure.Velocity) (p : SingularClosure.Pressure) : Prop where
  velocity_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Space => v z.1 z.2) (tailSpacetime δ)
  pressure_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) (tailSpacetime δ)
  divergence_free : ∀ t : ℝ, δ ≤ t → ∀ x : Space,
    SingularClosure.divergence (v t) x = 0
  equation : ∀ t : ℝ, δ ≤ t → ∀ x : Space,
    SingularClosure.timeDerivative v t x + SingularClosure.convection (v t) x +
        SingularClosure.gradient (p t) x = ν • SingularClosure.laplacian (v t) x
  pressure_normalized : ∀ t : ℝ, δ ≤ t → p t 0 = 0

/-- One smooth representative of the specified path at every tail time. -/
def HasSmoothTail (ν : ℝ) (u : Velocity) (δ : ℝ) : Prop :=
  ∃ (v : SingularClosure.Velocity) (p : SingularClosure.Pressure),
    ClassicalTail ν δ v p ∧
      ∀ t : ℝ, δ ≤ t → (u t : Space → Space) =ᵐ[volume] v t

/-- Exact original weak-gradient dissipation on every finite tail interval. -/
def TailEnergyEquality (ν : ℝ) (u : Velocity) (G : WeakGradient) (δ : ℝ) : Prop :=
  ∀ t : ℝ, δ ≤ t →
    ‖u t‖ ^ 2 + 2 * ν * (∫ r in δ..t, ∑ j : Fin 3, ‖G r j‖ ^ 2) = ‖u δ‖ ^ 2

/-- Equality of physical L2 velocity at every nonnegative time. -/
def SameVelocity (u v : Velocity) : Prop := ∀ t : ℝ, 0 ≤ t → u t = v t

/-- Full translated PDE membership from the exact own trace, and uniqueness
against every physical Leray--Hopf future from that trace. -/
def UniqueFuture (ν : ℝ) (u : Velocity) (G : WeakGradient) (δ : ℝ) : Prop :=
  LerayHopf ν (u δ) (fun t => u (δ + t)) (fun t => G (δ + t)) ∧
    ∀ (v : Velocity) (H : WeakGradient), LerayHopf ν (u δ) v H →
      SameVelocity (fun t => u (δ + t)) v

/-- The strict-cutoff QFA conclusion for one datum, including nonemptiness. -/
def DatumConclusion (ν : ℝ) (a : SpatialL2) : Prop :=
  (∃ (u : Velocity) (G : WeakGradient), LerayHopf ν a u G) ∧
    ∀ (u : Velocity) (G : WeakGradient), LerayHopf ν a u G →
      ∀ δ : ℝ, cutoff ν a < δ →
        HasSmoothTail ν u δ ∧ TailEnergyEquality ν u G δ ∧ UniqueFuture ν u G δ

/-- Stronger conclusion including the cutoff itself. Kept distinct from the
registered strict-cutoff root. -/
def ClosedDatumConclusion (ν : ℝ) (a : SpatialL2) : Prop :=
  (∃ (u : Velocity) (G : WeakGradient), LerayHopf ν a u G) ∧
    ∀ (u : Velocity) (G : WeakGradient), LerayHopf ν a u G →
      ∀ δ : ℝ, cutoff ν a ≤ δ →
        HasSmoothTail ν u δ ∧ TailEnergyEquality ν u G δ ∧ UniqueFuture ν u G δ

/-- Exact all-data physical QFA target; this definition supplies no witness. -/
def QuasiFeffermanA : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ a : EnergyDatum, DatumConclusion ν a.val

/-- Separately named stronger closed-cutoff all-data target. -/
def ClosedQuasiFeffermanA : Prop :=
  ∀ ν : ℝ, 0 < ν → ∀ a : EnergyDatum, ClosedDatumConclusion ν a.val

/-- The stronger closed-cutoff property implies the registered strict one. -/
theorem ClosedDatumConclusion.strict {ν : ℝ} {a : SpatialL2}
    (h : ClosedDatumConclusion ν a) : DatumConclusion ν a := by
  exact ⟨h.1, fun u G hu δ hδ => h.2 u G hu δ hδ.le⟩

end MethbokeAddon.QuasiFeffermanA.PhysicalRoot
