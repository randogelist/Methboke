import NavierStokes.ComparatorTheorem

/-!
# Fefferman D through the pinned upstream proof

This endpoint explicitly reuses the proof in
openai/NavierStokesAndEuler@f9e8bc5b38b6e212696e8a30e3e91517af887bbd.
It is checked in an isolated Lean4.34.0-rc2 project. It is not imported into
Material's Lean4.33.0 environment and does not assert the stronger prescribed-site
family theorem. The independent audit expands the initial-data, force and global
solution predicates into their physical conditions, including periodic pressure.
-/

set_option autoImplicit false

namespace Methboke.FeffermanD

/-- The classical periodic forced breakdown statement, for every positive
viscosity. This is a provenance-preserving application of the pinned upstream
proof, not a new singular seed construction. -/
theorem Fefferman_D (ν : ℝ) (hν : 0 < ν) :
    ∃ (u₀ : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3))
      (f : EuclideanSpace ℝ (Fin 3) → ℝ → EuclideanSpace ℝ (Fin 3)),
      NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀ ∧
      NavierStokes.Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ v p,
        NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic
          ν u₀ f v p) :=
  NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic ν hν

end Methboke.FeffermanD
