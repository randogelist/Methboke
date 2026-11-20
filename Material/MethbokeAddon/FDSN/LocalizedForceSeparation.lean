import MethbokeAddon.FDSN.LocalizedFront
import MethbokeAddon.FDSN.LocalizedPairSeparation
import MethbokeAddon.FDSN.FamilyContracts

/-!
# Projected-force separation for the concrete localized phase family

Both PDE fronts and both forces are the literal constructed families.
The only nonzero witness is an actual input Fourier coordinate at the
common normalization time. Its phase separation forces an unequal
Leray-projected force coefficient at an earlier interior time.
-/

set_option autoImplicit false

noncomputable section
open Set SingularClosure
open scoped ContDiff Topology

namespace MethbokeAddon.FDSN

theorem localizedPairForce_projected_separates
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (hsβ : s ∉ tsupport β) (hβt : β t = 1) (i : Fin 3)
    (hcoeff : datumFourierCoeff (u t) a i ≠ 0)
    {lambda eta : ℝ} (hlambda : |lambda| < Real.pi / 4)
    (heta : |eta| < Real.pi / 4) (hne : lambda ≠ eta) :
    ∃ r ∈ Ioo s t,
      coefficientLeray a (datumFourierCoeff (localizedPairForce ν a β u F lambda r) a) i ≠
        coefficientLeray a (datumFourierCoeff (localizedPairForce ν a β u F eta r) a) i := by
  have Hlambda := localizedPair_front h ha hβ hβs lambda
  have Heta := localizedPair_front h ha hβ hβs eta
  have hFlambda := localizedPairForce_admissible h a hβ hβc hβs lambda
  have hFeta := localizedPairForce_admissible h a hβ hβc hβs eta
  have htl : t ∈ Ico (0 : ℝ) T := ⟨(lt_of_lt_of_le hs hst).le, ht⟩
  have hinit : datumFourierCoeff (localizedPairVelocity a β u eta s) a i =
      datumFourierCoeff (localizedPairVelocity a β u lambda s) a i := by
    rw [localizedPairVelocity_eq_seed_off_support a u eta hsβ,
      localizedPairVelocity_eq_seed_off_support a u lambda hsβ]
  have hfinal : datumFourierCoeff (localizedPairVelocity a β u eta t) a i ≠
      datumFourierCoeff (localizedPairVelocity a β u lambda t) a i :=
    (localizedPairVelocity_coeff_ne_of_parameter_ne h ha htl hβt i hcoeff
      hlambda heta hne).symm
  obtain ⟨r, hr, hforce⟩ := Hlambda.projected_force_ne_of_pair_mode_ne Heta
    h.viscosity_pos.le s t hs hst ht a i
    (fun r _ => (hFlambda.smooth.comp
      (contDiff_const.prodMk contDiff_id)).continuous)
    (fun r _ => (hFeta.smooth.comp
      (contDiff_const.prodMk contDiff_id)).continuous)
    (fun r hr => localizedPairVelocity_difference_pairSupported h ha β lambda eta r
      ⟨(hs.trans hr.1).le, hr.2.trans ht⟩) hinit hfinal
  exact ⟨r, hr, hforce.symm⟩

/-- The concrete family satisfies the complete projected-force separation
clause using the same phase radius and selected Fourier pair. -/
theorem localizedPairForce_projectedSeparation
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) {β : ℝ → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hβc : HasCompactSupport β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (hsβ : s ∉ tsupport β) (hβt : β t = 1) (i : Fin 3)
    (hcoeff : datumFourierCoeff (u t) a i ≠ 0) :
    ProjectedForceSeparation T (Real.pi / 4) (localizedPairForce ν a β u F) := by
  intro lambda eta hlambda heta hne
  obtain ⟨r, hr, hforce⟩ := localizedPairForce_projected_separates h ha hβ hβc hβs
    s t hs hst ht hsβ hβt i hcoeff hlambda heta hne
  exact ⟨r, ⟨(hs.trans hr.1).le, hr.2.trans ht⟩, a, i, hforce⟩

end MethbokeAddon.FDSN
