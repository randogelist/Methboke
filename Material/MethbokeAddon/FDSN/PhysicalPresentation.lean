import MethbokeAddon.FDSN.Main
import MethbokeAddon.FDSN.PhysicalLerayAdapter

/-!
# The same FDSN family with a literal physical Leray witness

This is a presentation corollary of the constructed FDSN family. It keeps
every shared witness and every original clause, and adds a space-time point
where the actual Leray projection of each force difference is nonzero.
The stronger frame-array version includes every genuine fixed helical frame.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

noncomputable section

theorem FEFFERMAN_D_SPECTRAL_NONRIGIDITY_physical
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (hseed : Seed ν T u p F)
    (frame : HelicalFrameArray) (s : ℝ) (hs : s ∈ Ico (0 : ℝ) T) :
    ∃ a b tstar ε : ℝ, ∃ U G : ℝ → Velocity,
      s < a ∧ a < b ∧ b < T ∧ tstar ∈ Ioo a b ∧ 0 < ε ∧
      U 0 = u ∧ G 0 = F ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
        (U q.1 - u) q.2.1 q.2.2) {q | |q.1| < ε} ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
        (G q.1 - F) q.2.1 q.2.2) {q | |q.1| < ε} ∧
      ExactRealizationAndAgreement ν T a b ε u p F U G ∧
      CompleteHelicalPowerPreservation frame T ε u U ∧
      TranslationSeparation tstar ε U ∧
      ProjectedForceSeparation T ε G ∧
      SmoothSmallness a b ε u F U G ∧
      (∀ lambda eta : ℝ, |lambda| < ε → |eta| < ε → lambda ≠ eta →
        ∃ t ∈ Ico (0 : ℝ) T, ∃ x : Vec,
          physicalLerayProjection ((G lambda - G eta) t) x ≠ 0) := by
  obtain ⟨a, b, tstar, ε, U, G, hsa, hab, hbT, htstar, hε, hU0, hG0,
      hUsmooth, hGsmooth, hreal, hpower, htranslation, hprojected, hsmall⟩ :=
    hseed.familyFor frame s hs
  refine ⟨a, b, tstar, ε, U, G, hsa, hab, hbT, htstar, hε, hU0, hG0,
    hUsmooth, hGsmooth, hreal, hpower, htranslation, hprojected, hsmall, ?_⟩
  exact projectedForceSeparation_physical
    (fun lambda hlambda => (hreal lambda hlambda).2.1) hprojected

end

end MethbokeAddon.FDSN
