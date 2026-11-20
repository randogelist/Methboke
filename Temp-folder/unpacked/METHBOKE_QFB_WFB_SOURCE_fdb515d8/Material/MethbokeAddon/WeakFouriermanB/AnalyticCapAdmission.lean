import MethbokeAddon.WeakFouriermanB.FiniteCapAdmission
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-!
An actual analytic extension through the initial time supplies finite-cap
classical admission. The extension is an AnalyticOnNhd assertion for the actual
velocity and pressure on the open cylinder (-epsilon,T) x R^3; it is not a
formal Taylor recursion or an unproved convergence certificate.

The physical NSE equation in this interface is required only at nonnegative
times below T. The existing timeDerivative is a derivative within Ici 0, so it
must not be used here to assert an ordinary negative-time NSE equation. Thus
AnalyticForwardNSECap is a forward equation with an analytic extension through
zero, not a renamed claim that NSE holds on the entire negative-time cylinder.

The admission witness and strict cutoff inequality remain explicit. These
theorems neither construct the cap from a local analytic germ nor establish
the universal germ-to-cap assertion R1. Prepared source only; matching cached
external compiler, exact-type and axiom evidence remains required.
-/

set_option autoImplicit false

open Set SingularClosure QuasiFeffermanB
open scoped ContDiff

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

def analyticCapSpacetime (ε T : ℝ) : Set (ℝ × Vec) :=
  {z | -ε < z.1 ∧ z.1 < T}

/-- Literal analytic velocity and pressure through t=0, with the actual
forward physical equation, initial value and periodic mean-zero semantics.
Positivity of epsilon and viscosity are explicit hypotheses of admission.
-/
structure AnalyticForwardNSECap (ν ε T : ℝ) (a : Field)
    (u : Velocity) (p : Pressure) : Prop where
  velocity_analytic :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => u z.1 z.2) (analyticCapSpacetime ε T)
  pressure_analytic :
    AnalyticOnNhd ℝ (fun z : ℝ × Vec => p z.1 z.2) (analyticCapSpacetime ε T)
  velocity_periodic : ∀ t ∈ Ico (0 : ℝ) T, SpatialPeriodic (u t)
  pressure_periodic : ∀ t ∈ Ico (0 : ℝ) T, SpatialPeriodic (p t)
  divergence_free : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
      ν • laplacian (u t) x
  initial : u 0 = a
  velocity_mean_zero : ∀ t ∈ Ico (0 : ℝ) T, MeanZero (u t)
  pressure_mean_zero : ∀ t ∈ Ico (0 : ℝ) T, PressureMeanZero (p t)

theorem initial_front_subset_analytic_cap (ε T : ℝ) (hε : 0 < ε) :
    initialFrontSpacetime T ⊆ analyticCapSpacetime ε T := by
  intro z hz
  have hneg : -ε < 0 := by linarith
  exact ⟨hneg.trans_le hz.1, hz.2⟩

/-- Analytic regularity is converted to smoothness on the same existing
domain, then restricted to the actual nonnegative finite cylinder.
-/
theorem analytic_forward_cap_to_initial_classical
    (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hε : 0 < ε) (H : AnalyticForwardNSECap ν ε T a u p) :
    InitialClassicalFront ν T a u p := by
  have hsub := initial_front_subset_analytic_cap ε T hε
  have hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (analyticCapSpacetime ε T) := H.velocity_analytic.contDiffOn_of_completeSpace
  have hp : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2)
      (analyticCapSpacetime ε T) := H.pressure_analytic.contDiffOn_of_completeSpace
  exact {
    velocity_smooth := hu.mono hsub
    pressure_smooth := hp.mono hsub
    velocity_periodic := H.velocity_periodic
    pressure_periodic := H.pressure_periodic
    divergence_free := H.divergence_free
    equation := H.equation
    initial := H.initial
    velocity_mean_zero := H.velocity_mean_zero
    pressure_mean_zero := H.pressure_mean_zero
  }

/-- Conditional finite-cap analytic admission with the original literal QFB
cutoff. The resulting global pair retains the supplied velocity and pressure
at every nonnegative time strictly below the cap.
-/
theorem analytic_forward_cap_admission
    (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hε : 0 < ε)
    (hcap : cutoff (criticalL2Representative a) ν < T)
    (H : AnalyticForwardNSECap ν ε T a u p) :
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r :=
  finite_cap_classical_admission ν T a u p hν hcap
    (analytic_forward_cap_to_initial_classical ν ε T a u p hε H)

/-- The same criterion written in the physical-energy normalization:
tau_Q = (physicalEnergy a)^2 / (8*pi^2*nu^5). The admitted analytic front
supplies smooth datum admission, so no equality with a representative norm
is assumed separately.
-/
theorem analytic_forward_cap_admission_physical_cutoff
    (ν ε T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hε : 0 < ε)
    (hcap : (physicalEnergy a) ^ 2 / (8 * Real.pi ^ 2 * ν ^ 5) < T)
    (H : AnalyticForwardNSECap ν ε T a u p) :
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r := by
  have Hfront := analytic_forward_cap_to_initial_classical ν ε T a u p hε H
  have hnonneg : 0 ≤ (physicalEnergy a) ^ 2 / (8 * Real.pi ^ 2 * ν ^ 5) := by
    positivity
  have hT : 0 < T := hnonneg.trans_lt hcap
  have ha : SmoothSigmaZero a := initial_front_initial_smooth ν T a u p Hfront hT
  have hcut : cutoff (criticalL2Representative a) ν < T := by
    rw [smooth_datum_cutoff ha ν]
    exact hcap
  exact finite_cap_classical_admission ν T a u p hν hcut Hfront

end

end MethbokeAddon.WeakFouriermanB
