import MethbokeAddon.WeakFouriermanB.InitialFrontAdmission
import MethbokeAddon.WeakFouriermanB.FiniteCapOverlap
import QuasiFeffermanB.Cutoff
import QuasiFeffermanB.TailChain

/-!
Actual finite-cap classical admission through the original QFB cutoff.

The premise is an actual initial classical NSE pair on the half-open finite
cylinder, smooth up to time zero. Its horizon lies strictly beyond the literal
cutoff of the physical L2 representative of the same datum. The initial strong
trace and every shorter Serrin bound are derived from this pair. Q01 gives one
original weak path; finite-front comparison and Q09 identify both classical
pairs with that same path. Spatial continuity and normalized pressure then give
the actual overlap equalities used by the explicitly constructed smooth splice.

This is the conditional R0 admission step. It does not construct an initial
classical cap from arbitrary smooth data or extend an arbitrary analytic germ
to the cutoff. No global-solution or continuation field is an input premise.

Prepared source only; matching external cached compiler/type/axiom evidence is
pending. No local Lean execution. Staged outside active Material discovery.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure QuasiFeffermanB
open scoped ContDiff Topology

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

/-- An actual initial classical cap strictly beyond the QFB cutoff admits a
global smooth NSE pair preserving both its velocity and normalized pressure
throughout the original half-open cap. Existence of that finite cap is the
explicit admission premise; universal admission is not asserted.
-/
theorem finite_cap_classical_admission
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hcap : cutoff (criticalL2Representative a) ν < T)
    (H : InitialClassicalFront ν T a u p) :
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P ∧
      ∀ r ∈ Ico (0 : ℝ) T, U r = u r ∧ P r = p r := by
  have hcutoff0 : 0 ≤ cutoff (criticalL2Representative a) ν :=
    CUTOFF_NONNEG (criticalL2Representative a) hν
  have hT : 0 < T := hcutoff0.trans_lt hcap
  have ha : SmoothSigmaZero a := initial_front_initial_smooth ν T a u p H hT
  obtain ⟨w, G, hw, hw0, hfront⟩ :=
    initial_front_original_leray_hopf ν T a u p H hν hT
  let δ : ℝ := (cutoff (criticalL2Representative a) ν + T) / 2
  have hcutoffδ : cutoff (criticalL2Representative a) ν < δ := by
    dsimp [δ]
    linarith
  have hδT : δ < T := by
    dsimp [δ]
    linarith
  have hδ0 : 0 < δ := hcutoff0.trans_lt hcutoffδ
  obtain ⟨v, q, K, htail⟩ :=
    Q09_POST_CUTOFF_SMOOTHNESS hν (smooth_datum_energySigmaZero ha) hw hcutoffδ
  have hoverlap := finite_cap_tail_overlap_of_same_path_ae ν T δ a u v w p q
    H K hδ0.le
    (fun r hr => hfront r ⟨hδ0.trans hr.1, hr.2⟩)
    (fun r hr => htail r hr.1.le)
  obtain ⟨U, P, hglobal, hpreserve, hlate⟩ :=
    finite_cap_gluing ν T δ a u v p q H K hδ0.le hδT hoverlap.1 hoverlap.2
  exact ⟨U, P, hglobal, hpreserve⟩

end

end MethbokeAddon.WeakFouriermanB
