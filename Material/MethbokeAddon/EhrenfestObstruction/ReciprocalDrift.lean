import MethbokeAddon.EhrenfestObstruction.Definitions
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Exact reciprocal bounds and derivative

The derivative is obtained from the actual Galerkin coefficient-enstrophy
identity. No stopped-drift hypothesis is used in this module.
Candidate source; matching external cached type/axiom evidence is pending.
-/

set_option autoImplicit false

open Set Filter SingularClosure
open scoped Topology

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

theorem halfEnstrophy_nonneg (N : ℕ) (c : FourierCoeff) :
    0 ≤ halfEnstrophy N c := by
  exact div_nonneg (coefficientDissipation_nonneg N c) (by norm_num)

theorem reciprocal_denominator_pos (eStar : ℝ) (heStar : 0 < eStar)
    (N : ℕ) (c : FourierCoeff) :
    0 < 1 + halfEnstrophy N c / eStar := by
  have hq : 0 ≤ halfEnstrophy N c / eStar :=
    div_nonneg (halfEnstrophy_nonneg N c) heStar.le
  linarith

theorem reciprocalValue_bounds (eStar : ℝ) (heStar : 0 < eStar)
    (N : ℕ) (c : FourierCoeff) :
    0 < reciprocalValue eStar N c ∧ reciprocalValue eStar N c ≤ 1 := by
  have hden := reciprocal_denominator_pos eStar heStar N c
  have hq : 0 ≤ halfEnstrophy N c / eStar :=
    div_nonneg (halfEnstrophy_nonneg N c) heStar.le
  constructor
  · exact inv_pos.mpr hden
  · have hdiv : (1 : ℝ) / (1 + halfEnstrophy N c / eStar) ≤ 1 := by
      apply (div_le_iff₀ hden).2
      nlinarith
    simpa only [reciprocalValue, one_div] using hdiv

/-- The reciprocal identity for any actual finite Galerkin solution. -/
theorem galerkin_reciprocal_hasDerivWithinAt
    (ν : ℝ) (a : Field) (N : ℕ) (g : GalerkinSolution ν a N)
    (eStar : ℝ) (heStar : 0 < eStar) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt
      (fun r => reciprocalValue eStar N (g.coeff r))
      (reciprocalDrift ν eStar N (g.coeff t)) (Ici 0) t := by
  have hden : 1 + (coefficientDissipation N (g.coeff t) / 2) / eStar ≠ 0 := by
    exact ne_of_gt (reciprocal_denominator_pos eStar heStar N (g.coeff t))
  have hInner : HasDerivWithinAt
      (fun r : ℝ => 1 + (coefficientDissipation N (g.coeff r) / 2) / eStar)
      (((-2 * ν) * coefficientLaplacianSquare N (g.coeff t) -
        2 * coefficientEnstrophyNonlinearPower N (g.coeff t)) / 2 / eStar)
      (Ici 0) t :=
    (((g.coefficientEnstrophy_identity ht).div_const 2).div_const eStar).const_add 1
  have hOuter : HasDerivAt (fun x : ℝ => x⁻¹)
      (-((1 + (coefficientDissipation N (g.coeff t) / 2) / eStar) ^ 2)⁻¹)
      (1 + (coefficientDissipation N (g.coeff t) / 2) / eStar) :=
    hasDerivAt_inv hden
  -- Scalar composition can select the real inner-product module instance.
  -- The final convert! normalizes that instance diamond at default transparency.
  have hInv := hOuter.scomp_hasDerivWithinAt t hInner
  have hrate :
      (((-2 * ν) * coefficientLaplacianSquare N (g.coeff t) -
          2 * coefficientEnstrophyNonlinearPower N (g.coeff t)) / 2 / eStar) •
          (-((1 + (coefficientDissipation N (g.coeff t) / 2) / eStar) ^ 2)⁻¹) =
        reciprocalDrift ν eStar N (g.coeff t) := by
    simp only [smul_eq_mul, reciprocalDrift, halfEnstrophy, div_eq_mul_inv, mul_inv_rev]
    ring
  rw [hrate] at hInv
  convert! hInv using 1 <;>
    simp only [Function.comp_apply, reciprocalValue, halfEnstrophy]

theorem canonical_enstrophy_nonneg
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (n : ℕ) (t : ℝ) :
    0 ≤ canonicalEnstrophy ν hν a n t := by
  exact halfEnstrophy_nonneg (n + 1) ((canonicalFamily ν hν a n).coeff t)

theorem canonical_reciprocal_bounds
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ) (heStar : 0 < eStar) (n : ℕ) (t : ℝ) (_ht : 0 ≤ t) :
    0 < canonicalReciprocal ν hν a eStar n t ∧
      canonicalReciprocal ν hν a eStar n t ≤ 1 := by
  exact reciprocalValue_bounds eStar heStar (n + 1)
    ((canonicalFamily ν hν a n).coeff t)

theorem canonical_reciprocal_hasDerivWithinAt
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ) (heStar : 0 < eStar) (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (canonicalReciprocal ν hν a eStar n)
      (canonicalDrift ν hν a eStar n t) (Ici 0) t := by
  exact galerkin_reciprocal_hasDerivWithinAt ν a.val (n + 1)
    (canonicalFamily ν hν a n) eStar heStar t ht

theorem canonical_reciprocal_hasDerivAt
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ) (heStar : 0 < eStar) (n : ℕ) (t : ℝ) (ht : 0 < t) :
    HasDerivAt (canonicalReciprocal ν hν a eStar n)
      (canonicalDrift ν hν a eStar n t) t := by
  exact (canonical_reciprocal_hasDerivWithinAt ν hν a eStar heStar n t ht.le).hasDerivAt
    (Ici_mem_nhds ht)

theorem canonical_reciprocal_continuousOn_Ici
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ) (heStar : 0 < eStar) (n : ℕ) :
    ContinuousOn (canonicalReciprocal ν hν a eStar n) (Ici 0) := by
  intro t ht
  exact (canonical_reciprocal_hasDerivWithinAt ν hν a eStar heStar n t ht).continuousWithinAt

theorem canonical_reciprocal_continuousOn_Icc
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ) (heStar : 0 < eStar) (n : ℕ) (T : ℝ) :
    ContinuousOn (canonicalReciprocal ν hν a eStar n) (Icc 0 T) := by
  exact (canonical_reciprocal_continuousOn_Ici ν hν a eStar heStar n).mono
    (fun _ ht => ht.1)

end
end MethbokeAddon.EhrenfestObstruction
