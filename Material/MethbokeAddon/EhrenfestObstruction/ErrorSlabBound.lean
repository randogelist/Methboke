import MethbokeAddon.EhrenfestObstruction.ErrorState
import MethbokeAddon.EhrenfestObstruction.SmoothReference

/-!
The projected-reference part of the enstrophy reconstruction is derived from
an actual smooth front. The unit-error bound is still an explicit intermediate
premise awaiting the forced differential estimate and scalar bootstrap.
This is not the smooth-front Galerkin-bound endpoint or the obstruction root.
Prepared source only; external cached verification remains required.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open MethbokeAddon.WeakFouriermanB

namespace MethbokeAddon.EhrenfestObstruction

theorem smooth_front_eventual_slab_bound_of_unit_error
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S T : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (hTS : T < S)
    (herror : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t) ≤ 1) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      canonicalEnstrophy ν hν a n t ≤ C := by
  obtain ⟨K, hK, hreference⟩ :=
    initial_front_uniform_projected_dissipation ν S a.val u p H T hTS
  refine ⟨1 + K, eventual_canonical_slab_bound_of_error_and_reference
    ν hν a u T K herror ?_⟩
  intro n t ht
  exact hreference (n + 1) t ht

end MethbokeAddon.EhrenfestObstruction
