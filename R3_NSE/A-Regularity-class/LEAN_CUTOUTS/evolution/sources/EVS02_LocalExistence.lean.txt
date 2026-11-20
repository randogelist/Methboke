import MethbokeAddon.WeakFouriermanB.LocalGalerkinBounds
import MethbokeAddon.WeakFouriermanB.LocalGalerkinLimit

/-!
Actual local physical NSE construction for smooth initial data with a lifespan
controlled only by viscosity and an H1 bound. Finite Galerkin energy estimates
supply the local H2 seed, compactness constructs the untruncated Fourier flow,
and finite-window recovery gives the original datum, smooth velocity and
normalized pressure through the initial boundary. No local-solution, compactness,
continuation or AX6 premise occurs in the final existence statements.
Prepared source; matching external cached compiler/type/axiom evidence required.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped Interval

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- The explicit short-time bound constructs a smooth physical solution pair
for every smooth datum satisfying the stated enstrophy bound. -/
theorem local_initial_classical_front_exists
    (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (a : Field) (ha : SmoothSigmaZero a) (hinit : physicalDissipation a ≤ R) :
    ∃ u : Velocity, ∃ p : Pressure,
      InitialClassicalFront ν (localGalerkinTime ν R) a u p := by
  let T : ℝ := localGalerkinTime ν R
  let S : ℝ := 6 * (R + 1) * T + localGalerkinAccumulationBound ν R / ν
  have hT : 0 < T := localGalerkinTime_pos hν hR
  have hS : 0 ≤ S := by
    have hacc := localGalerkinAccumulationBound_nonneg (ν := ν) hR
    dsimp only [S]
    positivity
  have hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S := by
    intro N _hN g
    exact (galerkin_uniform_local_sobolev_bounds ν R hν hR a ha hinit N g).2.2
  obtain ⟨L, hL⟩ := local_sobolev_flow_of_uniform_H2 ν hν a ha T hT S hS hH2
  exact ⟨L.velocity, L.pressure, L.initialClassicalFront hT a ha hL⟩

/-- A single positive lifespan works for every smooth initial datum in the
specified physical H1 ball. Higher smooth norms affect regularity bounds only.
-/
theorem uniform_H1_local_initial_classical_front_exists
    (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R) :
    ∃ T : ℝ, 0 < T ∧ ∀ a : Field, SmoothSigmaZero a → physicalH1Square a ≤ R →
      ∃ u : Velocity, ∃ p : Pressure, InitialClassicalFront ν T a u p := by
  refine ⟨localGalerkinTime ν R, localGalerkinTime_pos hν hR, ?_⟩
  intro a ha hH1
  have hE : 0 ≤ physicalEnergy a := by
    rw [physicalEnergy_eq_integral_norm_sq]
    exact integral_nonneg (fun x => sq_nonneg ‖a x‖)
  have hinit : physicalDissipation a ≤ R := by
    change physicalEnergy a + physicalDissipation a ≤ R at hH1
    linarith
  exact local_initial_classical_front_exists ν R hν hR a ha hinit

end
end MethbokeAddon.WeakFouriermanB
