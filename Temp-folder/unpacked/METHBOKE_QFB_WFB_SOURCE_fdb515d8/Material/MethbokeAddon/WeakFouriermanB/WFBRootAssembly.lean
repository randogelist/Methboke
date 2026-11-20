import MethbokeAddon.WeakFouriermanB.MaximalClassicalFront
import MethbokeAddon.WeakFouriermanB.FiniteCapAdmission

/-!
# The strict-cutoff composition step for the WFB route

An actual maximal classical trajectory whose lifetime lies strictly beyond
the original physical QFB cutoff supplies a finite initial cap. The accepted
classical R0 admission theorem is applied once to that cap. Its one global
velocity/pressure pair agrees with every shorter part of the original path by
the proved maximal-front agreement property. The no-extension property then
forces the lifetime to be infinite.

Strict cutoff overlap remains an explicit premise. This module does not infer
it from a Fourier budget, construct a local lifespan, or prove the full WFB
criterion. Prepared source; matching external cached compiler/type/axiom
verification is required. No local Lean, Lake or kernel execution was used.
-/

set_option autoImplicit false

open Set SingularClosure QuasiFeffermanB
open scoped ENNReal

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Strict overlap with the literal QFB cutoff gives one global physical pair
preserving the whole original maximal velocity and normalized pressure, and
forces the maximal lifetime to be infinite. The strict-cutoff premise is not
derived here from the WFB Fourier-budget hypothesis. -/
theorem maximal_classical_front_global_of_strict_cutoff
    (ν : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (H : MaximalClassicalFront ν a u p Tmax)
    (hcut : ENNReal.ofReal (cutoff (criticalL2Representative a) ν) < Tmax) :
    Tmax = ⊤ ∧ ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ t : ℝ, 0 ≤ t → ENNReal.ofReal t < Tmax → U t = u t ∧ P t = p t := by
  have hcut0 : 0 ≤ cutoff (criticalL2Representative a) ν :=
    CUTOFF_NONNEG (criticalL2Representative a) hν
  obtain ⟨T, _, hcutT, hTmax⟩ := ENNReal.lt_iff_exists_real_btwn.mp hcut
  have hcutTreal : cutoff (criticalL2Representative a) ν < T :=
    (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hcut0).mp hcutT
  have hT : 0 < T := hcut0.trans_lt hcutTreal
  obtain ⟨U, P, hglobal, _⟩ := finite_cap_classical_admission ν T a u p
    hν hcutTreal (H.finite_front T hT hTmax)
  have htop : Tmax = ⊤ := by
    by_contra hfinite
    have hlarge : 0 < Tmax.toReal + 1 := by positivity
    have hbound : ENNReal.ofReal (Tmax.toReal + 1) ≤ Tmax :=
      H.no_extension (Tmax.toReal + 1) U P hlarge
        (global_smooth_to_initial_front ν (Tmax.toReal + 1) a U P hglobal)
    have hstrict : Tmax < ENNReal.ofReal (Tmax.toReal + 1) := by
      calc
        Tmax = ENNReal.ofReal Tmax.toReal := (ENNReal.ofReal_toReal hfinite).symm
        _ < ENNReal.ofReal (Tmax.toReal + 1) :=
          (ENNReal.ofReal_lt_ofReal_iff_of_nonneg ENNReal.toReal_nonneg).mpr
            (by linarith)
    exact (not_lt_of_ge hbound) hstrict
  refine ⟨htop, U, P, hglobal, ?_⟩
  intro t ht _
  have hwindow : 0 < t + 1 := by linarith
  have hagree := H.agreement (t + 1) U P hwindow
    (global_smooth_to_initial_front ν (t + 1) a U P hglobal)
    t ⟨ht, by linarith⟩
  exact ⟨hagree.1.symm, hagree.2.symm⟩

end
end MethbokeAddon.WeakFouriermanB
