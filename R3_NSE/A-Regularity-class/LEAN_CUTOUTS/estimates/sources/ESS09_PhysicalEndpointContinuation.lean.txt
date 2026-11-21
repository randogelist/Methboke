import MethbokeAddon.WeakFouriermanB.PhysicalBudgetContinuation
import MethbokeAddon.WeakFouriermanB.StrongContinuation

/-!
The actual physical enstrophy-square budget extends a finite classical front
beyond its endpoint, preserving its velocity and normalized pressure. The
derived uniform physical H1 bound supplies a common positive restart time;
restarting before the old endpoint and gluing yields a longer actual front.
No endpoint value, trace or regularity is used. Consequently a finite maximal
endpoint cannot have this budget on its whole open pre-endpoint interval.

This theorem concerns arbitrary actual classical trajectories and has no
Fourier or Galerkin hypothesis. Prepared source only; matching external
cached compilation and fresh exact-type/axiom audits remain required.
No local Lean, Lake, kernel audit or project test was executed.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped ENNReal

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Finite actual physical enstrophy-square integral yields a genuine longer
classical front preserving the entire old velocity and normalized pressure.
All restart information is derived from the actual front and the budget.
-/
theorem initial_front_extends_of_dissipation_square
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) T))) :
    ∃ S : ℝ, T < S ∧ ∃ (U : Velocity) (P : Pressure),
      InitialClassicalFront ν S a U P ∧
        ∀ t ∈ Ico (0 : ℝ) T, U t = u t ∧ P t = p t := by
  obtain ⟨R, hR, hbound⟩ := initial_front_uniform_H1_of_dissipation_square
    ν T a u p hν hT H hD
  obtain ⟨h, hh, hlocal⟩ := uniform_H1_local_initial_classical_front_exists ν R hν hR
  let s : ℝ := max (T / 2) (T - h / 2)
  have hs0 : 0 ≤ s :=
    (by linarith : 0 ≤ T / 2).trans (le_max_left (T / 2) (T - h / 2))
  have hsT : s < T := max_lt (by linarith) (by linarith)
  have hreach : T < s + h := by
    have hnear : T - h / 2 ≤ s := le_max_right (T / 2) (T - h / 2)
    linarith
  have hdata : SmoothSigmaZero (u s) :=
    initial_front_smooth_slices ν T a u p H s ⟨hs0, hsT⟩
  obtain ⟨v, q, K⟩ := hlocal (u s) hdata (hbound s ⟨hs0, hsT⟩)
  obtain ⟨U, P, Hlong, hagree, _⟩ := initial_front_extend_from_restart
    ν T s h a u v p q hν H ⟨hs0, hsT⟩ hh K hreach
  exact ⟨s + h, hreach, U, P, Hlong, hagree⟩

/-- A finite maximal classical lifetime cannot have finite actual physical
enstrophy-square integral over its entire open pre-endpoint interval.
-/
theorem maximal_classical_front_no_finite_dissipation_square
    (ν : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (H : MaximalClassicalFront ν a u p Tmax)
    (hfinite : Tmax ≠ ⊤)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) Tmax.toReal))) : False := by
  have hT : 0 < Tmax.toReal := ENNReal.toReal_pos H.lifetime_pos.ne' hfinite
  have HF := maximal_classical_front_restrict_le ν Tmax.toReal a u p Tmax H hT
    (ENNReal.ofReal_toReal hfinite).le
  obtain ⟨R, _, hR⟩ := initial_front_uniform_H1_of_dissipation_square
    ν Tmax.toReal a u p hν hT HF hD
  have htop : Tmax = ⊤ := maximal_classical_lifetime_eq_top_of_uniform_H1
    ν R a u p Tmax hν H (by
      intro t ht htmax
      exact hR t ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht hfinite).mp htmax⟩)
  exact hfinite htop

end
end MethbokeAddon.WeakFouriermanB
