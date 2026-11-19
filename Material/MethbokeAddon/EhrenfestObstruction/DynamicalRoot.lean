import MethbokeAddon.EhrenfestObstruction.EventualEnstrophyBound
import MethbokeAddon.EhrenfestObstruction.CanonicalBarrier
import MethbokeAddon.WeakFouriermanB.LocalClassicalUniqueness

/-!
The conditional dynamical obstruction for the actual canonical Galerkin
family. Smooth-front stability is derived by EventualEnstrophyBound; it is
not a new premise. The stopped-drift witness remains an explicit hypothesis.
Prepared source only, pending matching external compilation and audits.
-/

set_option autoImplicit false
open Set Filter SingularClosure
open MethbokeAddon.WeakFouriermanB

namespace MethbokeAddon.EhrenfestObstruction

/-- The stopped drift excludes an actual smooth front extending strictly
past its reciprocal-clock horizon. -/
theorem stopped_forbids_initial_front
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ)
    (hStopped : StoppedForDatum ν hν a eStar gamma R)
    (S : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p)
    (hTS : 1 / gamma < S) : False := by
  exact stopped_rejects_eventual_slab_bound ν hν a eStar gamma R hStopped
    (initial_front_eventual_canonical_enstrophy_bound
      ν hν a S (1 / gamma) u p H hTS)

/-- For the single fixed stopped datum, a global smooth NSE pair is impossible. -/
theorem stopped_forbids_global_smooth
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ)
    (hStopped : StoppedForDatum ν hν a eStar gamma R)
    (u : Velocity) (p : Pressure)
    (H : GlobalSmoothNSE ν a.val u p) : False := by
  exact stopped_forbids_initial_front ν hν a eStar gamma R hStopped
    (1 / gamma + 1) u p
    (global_smooth_to_initial_front ν (1 / gamma + 1) a.val u p H)
    (lt_add_one _)

/-- The exact coefficient-dynamical implication, with a single explicit
stopped-bound hypothesis. No operator realization or singular witness is
assumed as an additional field. -/
theorem EHRENFEST_OBSTRUCTION_DYNAMICAL
    (ν : ℝ) (hν : 0 < ν)
    (hStopped : StoppedCommutatorBound ν) : Not (NSE_B ν) := by
  intro hNSE
  rcases hStopped with ⟨_hν, a, eStar, gamma, R, hStop⟩
  obtain ⟨u, p, H⟩ := hNSE a.val a.property
  exact stopped_forbids_global_smooth ν hν a eStar gamma R hStop u p H

end MethbokeAddon.EhrenfestObstruction
