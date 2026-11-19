import MethbokeAddon.EhrenfestObstruction.CanonicalErrorInequality
import MethbokeAddon.EhrenfestObstruction.ErrorSlabBound
import MethbokeAddon.EhrenfestObstruction.SmallForcingBootstrap
import Mathlib.Analysis.SpecificLimits.Basic

/-!
Eventual canonical Galerkin enstrophy bounds from an actual smooth initial
front. The error differential inequality, its small forcing, the scalar
bootstrap and the projected-reference bound are all derived internally.
The final theorem has no assumed uniform Galerkin or error bound.

Prepared source only: every dependency and this endpoint still require
matching authorized external cached compilation and axiom auditing.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped BigOperators Topology

namespace MethbokeAddon.EhrenfestObstruction

noncomputable section

/-- The actual error coefficients are continuous up to the initial boundary. -/
theorem canonicalErrorCoeff_continuousOn_Icc
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S T : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (hTS : T < S)
    (n : ℕ) (k : Frequency) (i : Fin 3) :
    ContinuousOn (fun t => canonicalErrorCoeff ν hν a u n t k i)
      (Icc (0 : ℝ) T) := by
  have hc : ContinuousOn (fun t => (canonicalFamily ν hν a n).coeff t k i)
      (Icc (0 : ℝ) T) :=
    ((canonicalFamily ν hν a n).coefficient_continuous k i).mono (fun t ht => ht.1)
  have hv := initial_front_cutoff_fourier_continuousOn_Icc
    ν S a.val u p H (n + 1) k i T hTS
  change ContinuousOn (fun t => (canonicalFamily ν hν a n).coeff t k i -
    cutoffCoeff (n + 1) (datumFourierCoeff (u t)) k i) (Icc (0 : ℝ) T)
  convert! hc.sub hv using 1

/-- Finite summation gives closed-slab continuity of the actual H1 error square. -/
theorem canonical_error_dissipation_continuousOn_Icc
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S T : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (hTS : T < S) (n : ℕ) :
    ContinuousOn
      (fun t => coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t))
      (Icc (0 : ℝ) T) := by
  unfold coefficientDissipation
  apply continuousOn_finset_sum
  intro k hk
  apply continuousOn_finset_sum
  intro i hi
  exact continuousOn_const.mul
    (Complex.continuous_normSq.comp_continuousOn
      (canonicalErrorCoeff_continuousOn_Icc ν hν a S T u p H hTS n k i))

/-- The forcing rate at the literal nonzero cutoff tends to zero. -/
theorem forcing_div_nat_succ_sq_tendsto_zero (A : ℝ) :
    Tendsto (fun n : ℕ => A / (((n + 1 : ℕ) : ℝ) ^ 2)) atTop (𝓝 0) := by
  have h :=
    ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).pow 2).const_mul A
  simpa [div_eq_mul_inv, inv_pow] using h

/-- Actual smooth-front boundedness of the canonical spectral approximants.

The smooth physical front is the only analytic hypothesis. In particular,
the eventual unit error and enstrophy bounds are conclusions of the proof.
The cutoff is always `n+1` and the physical datum is fixed for all indices.
-/
theorem initial_front_eventual_canonical_enstrophy_bound
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S T : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (hTS : T < S) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      canonicalEnstrophy ν hν a n t ≤ C := by
  obtain ⟨C, A, hC, hA, hdiff⟩ :=
    initial_front_canonical_error_differential_inequality ν hν a S T u p H hTS
  let D : ℕ → ℝ → ℝ := fun n t =>
    coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t)
  have herror : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T, D n t ≤ 1 := by
    apply eventually_guarded_cubic_unit_bound_interior
      (D := D) (d := fun n t => deriv (D n) t)
      (epsilon := fun n => A / (((n + 1 : ℕ) : ℝ) ^ 2)) hC.le
    · exact Filter.Eventually.of_forall (fun n => by positivity)
    · exact forcing_div_nat_succ_sq_tendsto_zero A
    · intro n
      exact canonical_error_dissipation_continuousOn_Icc ν hν a S T u p H hTS n
    · intro n
      exact (canonical_error_initial_dissipation ν hν a u H.initial n).le
    · intro n t ht
      obtain ⟨rate, hrate, hbound⟩ := hdiff n t ht
      exact hrate.differentiableAt.hasDerivAt
    · intro n t ht hunit
      obtain ⟨rate, hrate, hbound⟩ := hdiff n t ht
      have hderiv : deriv (D n) t = rate := hrate.deriv
      change deriv (D n) t ≤ _
      rw [hderiv]
      exact hbound
  exact smooth_front_eventual_slab_bound_of_unit_error ν hν a S T u p H hTS herror

end

end MethbokeAddon.EhrenfestObstruction
