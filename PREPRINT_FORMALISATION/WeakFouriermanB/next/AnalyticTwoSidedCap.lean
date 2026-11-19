import MethbokeAddon.WeakFouriermanB.AnalyticCapAdmission
import Mathlib.Analysis.Calculus.Deriv.Basic

/-!
Literal two-sided analytic NSE cap and its forward physical adapter.

Unlike the earlier forward interface, the equation here holds throughout
(-epsilon,T), including negative times, and uses the ordinary derivative
deriv (fun r => u r x) t. Actual joint analyticity supplies ordinary temporal
differentiability. At every nonnegative time in the cap, including t=0,
unique differentiability of Ici 0 identifies the ordinary derivative with
SingularClosure.timeDerivative. Thus no negative-time meaning is assigned
to the derivative-within-Ici operator.

The record is the literal physical analytic-cap witness in the frozen G_nu
scope, with epsilon>0 and T beyond the cutoff supplied explicitly by the
admission theorem. This file does not construct such a cap from a local germ,
and leaves the universal germ-to-cap assertion R1 unresolved.

Prepared source only, outside active Material registration. No local Lean,
Lake, kernel audit or executable control tests have been run.
-/

set_option autoImplicit false

open Set SingularClosure QuasiFeffermanB
open scoped ContDiff Topology

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

/-- Actual joint analyticity yields an ordinary temporal derivative at each
time strictly inside the analytic cylinder, including negative times.
-/
theorem analytic_cap_time_differentiableAt
    (ε T : ℝ) (u : Velocity)
    (hu : AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) (analyticCapSpacetime ε T))
    (t : ℝ) (ht : t ∈ Ioo (-ε) T) (x : Vec) :
    DifferentiableAt ℝ (fun r : ℝ => u r x) t := by
  have hjoint : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (analyticCapSpacetime ε T) := hu.contDiffOn_of_completeSpace
  have htime : ContDiffOn ℝ ∞ (fun r : ℝ => u r x) (Ioo (-ε) T) :=
    hjoint.comp (contDiff_id.prodMk contDiff_const).contDiffOn (fun r hr => hr)
  exact (htime.differentiableOn (by simp) t ht).differentiableAt
    (isOpen_Ioo.mem_nhds ht)

/-- Ordinary and physical forward derivatives coincide at t=0 as well as at
positive times. The nonnegative-time hypothesis is essential to this adapter.
-/
theorem analytic_cap_forward_timeDerivative_eq_deriv
    (ε T : ℝ) (u : Velocity)
    (hu : AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) (analyticCapSpacetime ε T))
    (t : ℝ) (ht : t ∈ Ioo (-ε) T) (ht0 : 0 ≤ t) (x : Vec) :
    timeDerivative u t x = deriv (fun r : ℝ => u r x) t := by
  have hd := analytic_cap_time_differentiableAt ε T u hu t ht x
  exact hd.hasDerivAt.hasDerivWithinAt.derivWithin ((uniqueDiffOn_Ici 0) t ht0)

/-- Literal jointly analytic NSE evolution on the full open two-sided cap.
Every equation and spatial constraint applies on that same actual interval.
Initial value is an equality of the physical fields, not merely a jet.
-/
structure AnalyticTwoSidedNSECap (ν ε T : ℝ) (a : Field)
    (u : Velocity) (p : Pressure) : Prop where
  velocity_analytic :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) (analyticCapSpacetime ε T)
  pressure_analytic :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => p z.1 z.2) (analyticCapSpacetime ε T)
  velocity_periodic : ∀ t ∈ Ioo (-ε) T, SpatialPeriodic (u t)
  pressure_periodic : ∀ t ∈ Ioo (-ε) T, SpatialPeriodic (p t)
  divergence_free : ∀ t ∈ Ioo (-ε) T, ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t ∈ Ioo (-ε) T, ∀ x : Vec,
    deriv (fun r : ℝ => u r x) t + convection (u t) x + SingularClosure.gradient (p t) x =
      ν • laplacian (u t) x
  initial : u 0 = a
  velocity_mean_zero : ∀ t ∈ Ioo (-ε) T, MeanZero (u t)
  pressure_mean_zero : ∀ t ∈ Ioo (-ε) T, PressureMeanZero (p t)

/-- Restrict the full analytic solution to the forward physical interface.
The derivative conversion is proved rather than assumed in a record field.
-/
theorem analytic_two_sided_cap_to_forward
    (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hε : 0 < ε) (H : AnalyticTwoSidedNSECap ν ε T a u p) :
    AnalyticForwardNSECap ν ε T a u p := by
  have hsub : Ico (0 : ℝ) T ⊆ Ioo (-ε) T := by
    intro t ht
    have hneg : -ε < 0 := by linarith
    exact ⟨hneg.trans_le ht.1, ht.2⟩
  refine {
    velocity_analytic := H.velocity_analytic
    pressure_analytic := H.pressure_analytic
    velocity_periodic := fun t ht => H.velocity_periodic t (hsub ht)
    pressure_periodic := fun t ht => H.pressure_periodic t (hsub ht)
    divergence_free := fun t ht => H.divergence_free t (hsub ht)
    equation := ?_
    initial := H.initial
    velocity_mean_zero := fun t ht => H.velocity_mean_zero t (hsub ht)
    pressure_mean_zero := fun t ht => H.pressure_mean_zero t (hsub ht)
  }
  intro t ht x
  rw [analytic_cap_forward_timeDerivative_eq_deriv ε T u H.velocity_analytic
    t (hsub ht) ht.1 x]
  exact H.equation t (hsub ht) x

/-- The actual two-sided analytic cap, strictly beyond the original QFB
cutoff, yields a global smooth pair preserving the full forward cap.
-/
theorem analytic_two_sided_cap_admission
    (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hε : 0 < ε)
    (hcap : cutoff (criticalL2Representative a) ν < T)
    (H : AnalyticTwoSidedNSECap ν ε T a u p) :
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r :=
  analytic_forward_cap_admission ν ε T a u p hν hε hcap
    (analytic_two_sided_cap_to_forward ν ε T a u p hε H)

/-- Literal physical-energy cutoff version of the two-sided cap theorem.
The full analytic witness remains an explicit premise; universal existence
or extension of such a witness is not asserted.
-/
theorem analytic_two_sided_cap_admission_physical_cutoff
    (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hε : 0 < ε)
    (hcap : (physicalEnergy a) ^ 2 / (8 * Real.pi ^ 2 * ν ^ 5) < T)
    (H : AnalyticTwoSidedNSECap ν ε T a u p) :
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r :=
  analytic_forward_cap_admission_physical_cutoff ν ε T a u p hν hε hcap
    (analytic_two_sided_cap_to_forward ν ε T a u p hε H)

end

end MethbokeAddon.WeakFouriermanB
