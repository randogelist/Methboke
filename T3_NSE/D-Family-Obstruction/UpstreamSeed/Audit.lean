import MethbokeFeffermanD.Endpoint

/-!
Independent consumer signatures and literal semantic checks for Fefferman D.
The predicate expansions below are prepared from the pinned comparator reference,
whose original definitions are Copyright2026 The Formal Conjectures Authors,
Apache-2.0. No challenge theorem (which contains intentional placeholders) is
imported. The build imports only the upstream proof closure and this endpoint.
-/

set_option autoImplicit false
set_option pp.universes true
set_option pp.fullNames true

open ContDiff Set InnerProductSpace MeasureTheory
open scoped Laplacian

namespace Methboke.FeffermanD.Audit

abbrev Space := EuclideanSpace ℝ (Fin 3)

-- Literal initial-data contract: no mean-zero or smallness requirement.
example (u₀ : Space → Space) :
    NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀ ↔
      (∀ x, (fderiv ℝ u₀ x).trace ℝ Space = 0) ∧
      ContDiff ℝ ∞ u₀ ∧
      (∀ x i, u₀ (x + EuclideanSpace.single i 1) = u₀ x) := by
  constructor
  · intro h
    exact ⟨h.div_free, h.smooth, h.isOnePeriodic⟩
  · rintro ⟨hd, hs, hp⟩
    exact { div_free := hd, smooth := hs, isOnePeriodic := hp }

-- Literal force contract: every finite derivative order and every real decay exponent.
example (f : Space → ℝ → Space) :
    NavierStokes.Comparator.ForceConditionPeriodic f ↔
      ContDiffOn ℝ ∞ (fun z : Space × ℝ => f z.1 z.2) (univ ×ˢ Ici 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x i,
        f (x + EuclideanSpace.single i 1) t = f x t) ∧
      (∀ m : ℕ, ∀ K : ℝ, ∃ C : ℝ, ∀ x : Space, ∀ t : ℝ, 0 ≤ t →
        ‖iteratedFDerivWithin ℝ m (fun z : Space × ℝ => f z.1 z.2)
          (univ ×ˢ Ici 0) (x, t)‖ ≤ C / (1 + t) ^ K) := by
  constructor
  · intro h
    exact ⟨h.smooth, h.isOnePeriodic, h.decay⟩
  · rintro ⟨hs, hp, hd⟩
    exact { smooth := hs, isOnePeriodic := hp, decay := hd }

-- Literal competitor contract: actual PDE, right derivative at0, periodic pressure,
-- and no added global energy, pressure-gauge or zero-mean restriction.
example (ν : ℝ) (u₀ : Space → Space) (f v : Space → ℝ → Space)
    (p : Space → ℝ → ℝ) :
    NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic ν u₀ f v p ↔
      (∀ x : Space, ∀ t : ℝ, 0 ≤ t →
        derivWithin (fun s => v x s) (Ici 0) t +
          fderiv ℝ (fun y => v y t) x (v x t) =
        ν • Δ (fun y => v y t) x - gradient (fun y => p y t) x + f x t) ∧
      (∀ x : Space, ∀ t : ℝ, 0 ≤ t →
        (fderiv ℝ (fun y => v y t) x).trace ℝ Space = 0) ∧
      (∀ x : Space, v x 0 = u₀ x) ∧
      ContDiffOn ℝ ∞ (fun z : Space × ℝ => v z.1 z.2) (univ ×ˢ Ici 0) ∧
      ContDiffOn ℝ ∞ (fun z : Space × ℝ => p z.1 z.2) (univ ×ˢ Ici 0) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x i,
        v (x + EuclideanSpace.single i 1) t = v x t) ∧
      (∀ t : ℝ, 0 ≤ t → ∀ x i,
        p (x + EuclideanSpace.single i 1) t = p x t) := by
  constructor
  · intro h
    exact ⟨h.navier_stokes, h.div_free, h.initial_condition,
      h.velocity_smooth, h.pressure_smooth,
      h.isOnePeriodic_velocity, h.isOnePeriodic_pressure⟩
  · rintro ⟨heq, hd, hi, hv, hp, hvper, hpper⟩
    exact {
      navier_stokes := heq
      div_free := hd
      initial_condition := hi
      velocity_smooth := hv
      pressure_smooth := hp
      isOnePeriodic_velocity := hvper
      isOnePeriodic_pressure := hpper }

-- Independent full consumer signatures for both the imported proof and endpoint.
example (ν : ℝ) (hν : 0 < ν) :
    ∃ (u₀ : Space → Space) (f : Space → ℝ → Space),
      NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀ ∧
      NavierStokes.Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ (v : Space → ℝ → Space) (p : Space → ℝ → ℝ),
        NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic
          ν u₀ f v p) :=
  NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic ν hν

example (ν : ℝ) (hν : 0 < ν) :
    ∃ (u₀ : Space → Space) (f : Space → ℝ → Space),
      NavierStokes.Comparator.InitialVelocityConditionPeriodic u₀ ∧
      NavierStokes.Comparator.ForceConditionPeriodic f ∧
      ¬ (∃ (v : Space → ℝ → Space) (p : Space → ℝ → ℝ),
        NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic
          ν u₀ f v p) :=
  Methboke.FeffermanD.Fefferman_D ν hν

end Methboke.FeffermanD.Audit

#eval IO.println "TYPE_BEGIN:NavierStokes.Comparator.InitialVelocityConditionPeriodic"
#check @NavierStokes.Comparator.InitialVelocityConditionPeriodic
#eval IO.println "TYPE_END:NavierStokes.Comparator.InitialVelocityConditionPeriodic"
#eval IO.println "AXIOMS_BEGIN:NavierStokes.Comparator.InitialVelocityConditionPeriodic"
#print axioms NavierStokes.Comparator.InitialVelocityConditionPeriodic
#eval IO.println "AXIOMS_END:NavierStokes.Comparator.InitialVelocityConditionPeriodic"

#eval IO.println "TYPE_BEGIN:NavierStokes.Comparator.ForceConditionPeriodic"
#check @NavierStokes.Comparator.ForceConditionPeriodic
#eval IO.println "TYPE_END:NavierStokes.Comparator.ForceConditionPeriodic"
#eval IO.println "AXIOMS_BEGIN:NavierStokes.Comparator.ForceConditionPeriodic"
#print axioms NavierStokes.Comparator.ForceConditionPeriodic
#eval IO.println "AXIOMS_END:NavierStokes.Comparator.ForceConditionPeriodic"

#eval IO.println "TYPE_BEGIN:NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic"
#check @NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic
#eval IO.println "TYPE_END:NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic"
#eval IO.println "AXIOMS_BEGIN:NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic"
#print axioms NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic
#eval IO.println "AXIOMS_END:NavierStokes.Comparator.NavierStokesExistenceAndSmoothnessPeriodic"

#eval IO.println "TYPE_BEGIN:NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic"
#check @NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic
#eval IO.println "TYPE_END:NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic"
#eval IO.println "AXIOMS_BEGIN:NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic"
#print axioms NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic
#eval IO.println "AXIOMS_END:NavierStokes.ComparatorBridge.navier_stokes_breakdown_periodic"

#eval IO.println "TYPE_BEGIN:Methboke.FeffermanD.Fefferman_D"
#check @Methboke.FeffermanD.Fefferman_D
#eval IO.println "TYPE_END:Methboke.FeffermanD.Fefferman_D"
#eval IO.println "AXIOMS_BEGIN:Methboke.FeffermanD.Fefferman_D"
#print axioms Methboke.FeffermanD.Fefferman_D
#eval IO.println "AXIOMS_END:Methboke.FeffermanD.Fefferman_D"
