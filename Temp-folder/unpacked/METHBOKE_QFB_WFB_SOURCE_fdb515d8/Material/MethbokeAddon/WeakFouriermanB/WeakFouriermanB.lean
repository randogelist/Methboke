import MethbokeAddon.WeakFouriermanB.LocalExistence
import MethbokeAddon.WeakFouriermanB.StrictCutoff
import MethbokeAddon.WeakFouriermanB.WFBRootAssembly

/-!
# Weak_Fourierman_B: the full-budget conditional conclusion

The first theorem constructs a maximal classical trajectory for every smooth
periodic solenoidal mean-zero datum. Its proof uses the actual physical local
construction, not an assumed local-existence principle.

The root theorem retains exactly the full extended Fourier-square budget on
the open interval ending at the finite minimum of the maximal lifetime and
the physical QFB cutoff. Physical continuation proves strict overlap; the
classical R0 theorem then supplies one global solution pair preserving the
entire original velocity and normalized-pressure trajectory. The finite
minimum is taken before conversion to a real time, including infinite
lifetimes and zero cutoff. No universal budget-finiteness claim is made.

All proofs in this new dependency chain remain prepared source until matching
external cached compilation and fresh exact-type/axiom audits succeed. No
local Lean, Lake, kernel audit or executable project test was run.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure QuasiFeffermanB
open scoped ENNReal

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Every smooth datum has an actual maximal classical trajectory. The
norm-controlled physical local theorem discharges the existence premise of
the maximal-front construction; there is no `hLocal` argument here. -/
theorem smooth_datum_maximal_classical_front_exists
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a) :
    ∃ Tmax : ℝ≥0∞, ∃ (u : Velocity) (p : Pressure),
      MaximalClassicalFront ν a u p Tmax := by
  have hR : 0 ≤ physicalDissipation a :=
    integral_nonneg (gradientSquareDensity_nonneg a)
  obtain ⟨u, p, H⟩ := local_initial_classical_front_exists
    ν (physicalDissipation a) hν hR a ha le_rfl
  exact maximal_classical_front_exists_of_front
    ν (localGalerkinTime ν (physicalDissipation a)) a u p hν
    (localGalerkinTime_pos hν hR) H

/-- The full squared Fourier budget up to the smaller of the maximal lifetime
and the original physical cutoff forces infinite lifetime and gives one global
smooth pair agreeing with the entire original maximal velocity and normalized
pressure. Existence of maximal trajectories for all smooth data is proved
above. The budget remains an explicit analytic hypothesis. -/
theorem Weak_Fourierman_B
    (ν : ℝ) (hν : 0 < ν) (a : Field) (_ha : SmoothSigmaZero a)
    (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (H : MaximalClassicalFront ν a u p Tmax)
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t))
      (min Tmax (ENNReal.ofReal (cutoff (criticalL2Representative a) ν))).toReal) :
    Tmax = ⊤ ∧ ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax → U t = u t ∧ P t = p t := by
  have hstrict := maximal_classical_lifetime_strictly_exceeds_cutoff
    ν (cutoff (criticalL2Representative a) ν) a u p Tmax hν H hbudget
  exact maximal_classical_front_global_of_strict_cutoff ν a u p Tmax hν H hstrict

end
end MethbokeAddon.WeakFouriermanB
