import MethbokeAddon.WeakFouriermanB.MaximalClassicalFront
import MethbokeAddon.WeakFouriermanB.LocalExistence
import MethbokeAddon.WeakFouriermanB.FiniteFrontGluing

/-!
# Physical continuation from a uniform H1 bound

A single H1 bound below the maximal lifetime supplies a common positive
restart duration through the constructed physical local-existence theorem.
If the lifetime were finite, restarting strictly before it and gluing on an
interior overlap would give an admitted front with a strictly larger duration.
This contradicts the actual maximal front's no-extension property.

No field value, trace or regularity at a finite maximal endpoint is used.
Smoothness of the restart datum is derived from a shorter actual front.
No local-existence, restart or continuation assertion is assumed as an axiom.
Prepared source only; the entire dependency chain requires matching external
cached compilation and fresh exact-type/axiom audits. No local Lean ran.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped ENNReal

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

private theorem strongContinuation_physicalH1Square_nonneg (v : Field) :
    0 ≤ physicalH1Square v := by
  have hE : 0 ≤ physicalEnergy v := by
    rw [physicalEnergy_eq_integral_norm_sq]
    exact integral_nonneg (fun x => sq_nonneg ‖v x‖)
  have hD : 0 ≤ physicalDissipation v :=
    integral_nonneg (gradientSquareDensity_nonneg v)
  exact add_nonneg hE hD

/-- Uniform boundedness of the actual physical H1 square on the whole
pre-endpoint path excludes a finite maximal lifetime. The bound includes time
zero; its nonnegativity is derived rather than separately assumed.
-/
theorem maximal_classical_lifetime_eq_top_of_uniform_H1
    (ν R : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (H : MaximalClassicalFront ν a u p Tmax)
    (hbound : ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax →
      physicalH1Square (u t) ≤ R) : Tmax = ⊤ := by
  have hR : 0 ≤ R :=
    (strongContinuation_physicalH1Square_nonneg (u 0)).trans
      (hbound 0 le_rfl (by simpa only [ENNReal.ofReal_zero] using H.lifetime_pos))
  obtain ⟨h, hh, hlocal⟩ := uniform_H1_local_initial_classical_front_exists ν R hν hR
  by_contra hfinite
  let τ : ℝ := Tmax.toReal
  have hτ : 0 < τ := ENNReal.toReal_pos H.lifetime_pos.ne' hfinite
  let s : ℝ := max (τ / 2) (τ - h / 2)
  have hs0 : 0 ≤ s := by
    exact (by linarith : 0 ≤ τ / 2).trans (le_max_left (τ / 2) (τ - h / 2))
  have hsτ : s < τ := by
    exact max_lt (by linarith) (by linarith)
  have hreach : τ < s + h := by
    have hnear : τ - h / 2 ≤ s := le_max_right (τ / 2) (τ - h / 2)
    linarith
  let T : ℝ := (s + τ) / 2
  have hsT : s < T := by dsimp only [T]; linarith
  have hTτ : T < τ := by dsimp only [T]; linarith
  have hT : 0 < T := hs0.trans_lt hsT
  have hTmax : ENNReal.ofReal T < Tmax :=
    (ENNReal.ofReal_lt_iff_lt_toReal hT.le hfinite).mpr hTτ
  have hsmax : ENNReal.ofReal s < Tmax :=
    (ENNReal.ofReal_lt_iff_lt_toReal hs0 hfinite).mpr hsτ
  have HF : InitialClassicalFront ν T a u p := H.finite_front T hT hTmax
  have hdata : SmoothSigmaZero (u s) :=
    initial_front_smooth_slices ν T a u p HF s ⟨hs0, hsT⟩
  obtain ⟨v, q, K⟩ := hlocal (u s) hdata (hbound s hs0 hsmax)
  obtain ⟨U, P, Hlong, _⟩ := initial_front_extend_from_restart ν T s h a u v p q
    hν HF ⟨hs0, hsT⟩ hh K (hTτ.trans hreach)
  have hlong : ENNReal.ofReal (s + h) ≤ Tmax :=
    H.no_extension (s + h) U P (hτ.trans hreach) Hlong
  have hstrict : Tmax < ENNReal.ofReal (s + h) := by
    calc
      Tmax = ENNReal.ofReal τ := (ENNReal.ofReal_toReal hfinite).symm
      _ < ENNReal.ofReal (s + h) :=
        (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hτ.le).mpr hreach
  exact (not_le_of_gt hstrict) hlong

end
end MethbokeAddon.WeakFouriermanB
