import EhrenfestCanonical.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-!
Independent exact consumer types and literal-definition checks.
This file is prepared for external verification and was not executed locally.
-/

open Set Filter SingularClosure MethbokeAddon.EhrenfestObstruction

namespace EhrenfestCanonical.TypeChecks

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (n : ℕ) :
    canonicalFamily ν hν a n =
      canonicalGalerkinSolution ν hν a.val a.property (n + 1) := rfl

example (ν eStar : ℝ) (N : ℕ) (c : FourierCoeff) :
    reciprocalDrift ν eStar N c =
      (ν * coefficientLaplacianSquare N c + coefficientEnstrophyNonlinearPower N c) /
        (eStar * (1 + (coefficientDissipation N c / 2) / eStar) ^ 2) := rfl

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ) :
    StoppedForDatum ν hν a eStar gamma R ↔
      (0 < eStar ∧ 0 < gamma ∧ (∀ n : ℕ, 0 < R n) ∧
        Tendsto R atTop atTop ∧
          ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ t : ℝ,
            (0 ≤ t ∧ t < 1 / gamma ∧
              ∀ s : ℝ, 0 ≤ s → s ≤ t → canonicalEnstrophy ν hν a n s < R n) →
                canonicalDrift ν hν a eStar n t ≤ -gamma) := Iff.rfl

example (ν : ℝ) :
    StoppedCommutatorBound ν ↔
      (∃ hν : 0 < ν, ∃ a : SmoothDatum, ∃ eStar gamma : ℝ, ∃ R : ℕ → ℝ,
        StoppedForDatum ν hν a eStar gamma R) := Iff.rfl

example (ν : ℝ) :
    NSE_B ν ↔ (∀ a : Field, SmoothSigmaZero a →
      ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P) := Iff.rfl

example : ∀ (N : ℕ) (c : FourierCoeff), 0 ≤ halfEnstrophy N c :=
  @MethbokeAddon.EhrenfestObstruction.halfEnstrophy_nonneg

example : ∀ (eStar : ℝ), 0 < eStar → ∀ (N : ℕ) (c : FourierCoeff),
    0 < 1 + halfEnstrophy N c / eStar :=
  @MethbokeAddon.EhrenfestObstruction.reciprocal_denominator_pos

example : ∀ (eStar : ℝ), 0 < eStar → ∀ (N : ℕ) (c : FourierCoeff),
    0 < reciprocalValue eStar N c ∧ reciprocalValue eStar N c ≤ 1 :=
  @MethbokeAddon.EhrenfestObstruction.reciprocalValue_bounds

example : ∀ (ν : ℝ) (a : Field) (N : ℕ) (g : GalerkinSolution ν a N)
    (eStar : ℝ), 0 < eStar → ∀ (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (fun r => reciprocalValue eStar N (g.coeff r))
        (reciprocalDrift ν eStar N (g.coeff t)) (Ici 0) t :=
  @MethbokeAddon.EhrenfestObstruction.galerkin_reciprocal_hasDerivWithinAt

example : ∀ (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (n : ℕ) (t : ℝ),
    0 ≤ canonicalEnstrophy ν hν a n t :=
  @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_nonneg

example : ∀ (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ), 0 < eStar → ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      0 < canonicalReciprocal ν hν a eStar n t ∧
        canonicalReciprocal ν hν a eStar n t ≤ 1 :=
  @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_bounds

example : ∀ (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ), 0 < eStar → ∀ (n : ℕ) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (canonicalReciprocal ν hν a eStar n)
        (canonicalDrift ν hν a eStar n t) (Ici 0) t :=
  @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivWithinAt

example : ∀ (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ), 0 < eStar → ∀ (n : ℕ) (t : ℝ), 0 < t →
      HasDerivAt (canonicalReciprocal ν hν a eStar n)
        (canonicalDrift ν hν a eStar n t) t :=
  @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivAt

example : ∀ (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ), 0 < eStar → ∀ n : ℕ,
      ContinuousOn (canonicalReciprocal ν hν a eStar n) (Ici 0) :=
  @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Ici

example : ∀ (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ), 0 < eStar → ∀ (n : ℕ) (T : ℝ),
      ContinuousOn (canonicalReciprocal ν hν a eStar n) (Icc 0 T) :=
  @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Icc

example : ∀ (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ),
      StoppedForDatum ν hν a eStar gamma R →
        ¬ (∃ C : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) (1 / gamma),
          canonicalEnstrophy ν hν a n t ≤ C) :=
  @MethbokeAddon.EhrenfestObstruction.stopped_rejects_eventual_slab_bound

end EhrenfestCanonical.TypeChecks


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.halfEnstrophy_nonneg"
#check @MethbokeAddon.EhrenfestObstruction.halfEnstrophy_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.halfEnstrophy_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.halfEnstrophy_nonneg"
#print axioms MethbokeAddon.EhrenfestObstruction.halfEnstrophy_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.halfEnstrophy_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocal_denominator_pos"
#check @MethbokeAddon.EhrenfestObstruction.reciprocal_denominator_pos
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.reciprocal_denominator_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocal_denominator_pos"
#print axioms MethbokeAddon.EhrenfestObstruction.reciprocal_denominator_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.reciprocal_denominator_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocalValue_bounds"
#check @MethbokeAddon.EhrenfestObstruction.reciprocalValue_bounds
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.reciprocalValue_bounds"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocalValue_bounds"
#print axioms MethbokeAddon.EhrenfestObstruction.reciprocalValue_bounds
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.reciprocalValue_bounds"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.galerkin_reciprocal_hasDerivWithinAt"
#check @MethbokeAddon.EhrenfestObstruction.galerkin_reciprocal_hasDerivWithinAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.galerkin_reciprocal_hasDerivWithinAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.galerkin_reciprocal_hasDerivWithinAt"
#print axioms MethbokeAddon.EhrenfestObstruction.galerkin_reciprocal_hasDerivWithinAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.galerkin_reciprocal_hasDerivWithinAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_nonneg"
#check @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_nonneg"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_bounds"
#check @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_bounds
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_bounds"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_bounds"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_bounds
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_bounds"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivWithinAt"
#check @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivWithinAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivWithinAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivWithinAt"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivWithinAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivWithinAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivAt"
#check @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivAt"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Ici"
#check @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Ici
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Ici"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Ici"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Ici
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Ici"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_rejects_eventual_slab_bound"
#check @MethbokeAddon.EhrenfestObstruction.stopped_rejects_eventual_slab_bound
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.stopped_rejects_eventual_slab_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_rejects_eventual_slab_bound"
#print axioms MethbokeAddon.EhrenfestObstruction.stopped_rejects_eventual_slab_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.stopped_rejects_eventual_slab_bound"

