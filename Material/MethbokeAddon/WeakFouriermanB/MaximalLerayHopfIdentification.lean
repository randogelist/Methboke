import MethbokeAddon.WeakFouriermanB.MaximalClassicalFront

/-!
# One original Leray--Hopf trajectory on the whole maximal classical front

The comparison is made at every pre-endpoint time by restricting the actual
maximal trajectory to a strictly longer finite front. The original weak pair
is fixed before choosing that front. Its initial representative is the actual
physical L2 class of the smooth datum; equality at zero is included.

The existence theorem invokes Q01 once and retains that same witness through
all later comparisons. No global smooth reference or new weak-path existence
premise is assumed. Prepared source; matching external cached compilation and
fresh exact-type/axiom audits are required. No local Lean execution was used.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped ENNReal

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Every original weak trajectory from the same datum agrees with the actual
maximal classical velocity at every pre-endpoint time, including zero. -/
theorem maximal_front_leray_hopf_identification
    (ν : ℝ) (a : Field) (u v : Velocity) (p : Pressure)
    (G : QuasiFeffermanB.WeakGradientTrajectory) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (ha : SmoothSigmaZero a)
    (H : MaximalClassicalFront ν a u p Tmax)
    (hv : CriticalLerayHopf ν (criticalL2Representative a) v G) :
    ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax →
      v t =ᵐ[volume.restrict unitCube] u t := by
  intro t ht0 htmax
  rcases eq_or_lt_of_le ht0 with hzero | hpos
  · subst t
    have hinit : v 0 =ᵐ[volume.restrict unitCube] a :=
      hv.initial.trans (smooth_datum_representative_ae ha)
    simpa only [H.initial] using hinit
  · obtain ⟨T, _, htT, hTmax⟩ := ENNReal.lt_iff_exists_real_btwn.mp htmax
    have htTreal : t < T :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hpos.le).mp htT
    have hT : 0 < T := hpos.trans htTreal
    exact initial_front_leray_hopf_identification ν T a u p v G
      (H.finite_front T hT hTmax) hν hT hv t ⟨hpos, htTreal⟩

/-- Construct one original Q01 weak trajectory and identify that same witness
on the entire maximal classical front. Compact horizons are used only inside
the comparison proof, never to choose replacement weak trajectories. -/
theorem maximal_front_original_leray_hopf
    (ν : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (ha : SmoothSigmaZero a)
    (H : MaximalClassicalFront ν a u p Tmax) :
    ∃ (v : Velocity) (G : QuasiFeffermanB.WeakGradientTrajectory),
      CriticalLerayHopf ν (criticalL2Representative a) v G ∧
      (v 0 =ᵐ[volume.restrict unitCube] a) ∧
      ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax →
        v t =ᵐ[volume.restrict unitCube] u t := by
  obtain ⟨v, G, hv, hv0⟩ := smooth_datum_lerayHopf_exists ν hν a ha
  exact ⟨v, G, hv, hv0,
    maximal_front_leray_hopf_identification ν a u v p G Tmax hν ha H hv⟩

end
end MethbokeAddon.WeakFouriermanB
