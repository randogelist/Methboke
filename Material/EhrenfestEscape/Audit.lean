import EhrenfestEscape.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independently stated consumer types; fresh external evidence required. -/

/-! Prepared consumer types and axiom queries for authorized external checking. -/

open Set

namespace MethbokeAddon.EhrenfestObstruction.EscapeTypeChecks

example :
    ∀ (eStar e : ℝ), 0 < eStar → 0 ≤ e → 0 < 1 + e / eStar :=
  @MethbokeAddon.EhrenfestObstruction.scalar_reciprocal_denominator_pos

example :
    ∀ (eStar R : ℝ), 0 < eStar → 0 ≤ R → 0 < (1 + R / eStar)⁻¹ :=
  @MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_pos

example :
    ∀ (eStar e R : ℝ), 0 < eStar → 0 ≤ e → 0 ≤ R →
      ((1 + R / eStar)⁻¹ < (1 + e / eStar)⁻¹ ↔ e < R) :=
  @MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_strict_iff

example :
    ∀ (eStar e R : ℝ), 0 < eStar → 0 ≤ e → 0 ≤ R →
      ((1 + e / eStar)⁻¹ ≤ (1 + R / eStar)⁻¹ ↔ R ≤ e) :=
  @MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_weak_iff

example :
    ∀ (eStar e R : ℝ), 0 < eStar → 0 ≤ e → 0 ≤ R →
      ((1 + e / eStar)⁻¹ = (1 + R / eStar)⁻¹ ↔ e = R) :=
  @MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_eq_iff

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (eStar : ℝ), 0 < eStar → ∀ (n : ℕ) (t R : ℝ), 0 ≤ R →
      ((1 + R / eStar)⁻¹ <
          MethbokeAddon.EhrenfestObstruction.canonicalReciprocal ν hν a eStar n t ↔
        MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n t < R) :=
  @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_strict_iff

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (eStar : ℝ), 0 < eStar → ∀ (n : ℕ) (t R : ℝ), 0 ≤ R →
      (MethbokeAddon.EhrenfestObstruction.canonicalReciprocal ν hν a eStar n t ≤
          (1 + R / eStar)⁻¹ ↔
        R ≤ MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n t) :=
  @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_weak_iff

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (eStar : ℝ), 0 < eStar → ∀ (n : ℕ) (t R : ℝ), 0 ≤ R →
      (MethbokeAddon.EhrenfestObstruction.canonicalReciprocal ν hν a eStar n t =
          (1 + R / eStar)⁻¹ ↔
        MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n t = R) :=
  @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_eq_iff

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (eStar gamma R : ℝ) (n : ℕ),
      0 < eStar → 0 < gamma → 0 < R →
      MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n 0 < R →
      (∀ t : ℝ,
        MethbokeAddon.EhrenfestObstruction.PreHit
          (MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n)
          R (1 / gamma) t →
        MethbokeAddon.EhrenfestObstruction.canonicalDrift ν hν a eStar n t ≤ -gamma) →
      ∃ t ∈ Ico 0 (1 / gamma),
        MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n t = R :=
  @MethbokeAddon.EhrenfestObstruction.canonical_stopped_exact_threshold_hitting

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (eStar gamma R : ℝ) (n : ℕ),
      0 < eStar → 0 < gamma → 0 < R →
      (∀ t : ℝ,
        MethbokeAddon.EhrenfestObstruction.PreHit
          (MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n)
          R (1 / gamma) t →
        MethbokeAddon.EhrenfestObstruction.canonicalDrift ν hν a eStar n t ≤ -gamma) →
      ∃ t ∈ Ico 0 (1 / gamma),
        R ≤ MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n t :=
  @MethbokeAddon.EhrenfestObstruction.canonical_stopped_threshold_crossing

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (eStar gamma : ℝ) (R : ℕ → ℝ),
      MethbokeAddon.EhrenfestObstruction.StoppedForDatum ν hν a eStar gamma R →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ t ∈ Ico 0 (1 / gamma),
          R n ≤ MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n t :=
  @MethbokeAddon.EhrenfestObstruction.stopped_threshold_escape

end MethbokeAddon.EhrenfestObstruction.EscapeTypeChecks


/-! Exact consumer propositions and axiom queries for external checking only. -/

open Set Filter

namespace MethbokeAddon.EhrenfestObstruction.SupremumTypeChecks

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum) (n : ℕ),
      ContinuousOn (MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n)
        (Ici 0) :=
  @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Ici

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (n : ℕ) (T : ℝ),
      ContinuousOn (MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n)
        (Icc 0 T) :=
  @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Icc

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (n : ℕ) (T : ℝ),
      BddAbove (MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n '' Icc 0 T) :=
  @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_bddAbove_Icc

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (T : ℝ) (n : ℕ), 0 ≤ T →
      ∃ t ∈ Icc 0 T,
        MethbokeAddon.EhrenfestObstruction.canonicalSlabEnstrophySup ν hν a T n =
          MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n t :=
  @MethbokeAddon.EhrenfestObstruction.canonical_slab_enstrophy_sup_attained

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (T : ℝ) (n : ℕ) (t : ℝ), t ∈ Icc 0 T →
      MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n t ≤
        MethbokeAddon.EhrenfestObstruction.canonicalSlabEnstrophySup ν hν a T n :=
  @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_slab_sup

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (eStar gamma : ℝ) (R : ℕ → ℝ),
      MethbokeAddon.EhrenfestObstruction.StoppedForDatum ν hν a eStar gamma R →
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        R n ≤ MethbokeAddon.EhrenfestObstruction.canonicalSlabEnstrophySup
          ν hν a (1 / gamma) n :=
  @MethbokeAddon.EhrenfestObstruction.stopped_threshold_le_slab_sup

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (eStar gamma : ℝ) (R : ℕ → ℝ),
      MethbokeAddon.EhrenfestObstruction.StoppedForDatum ν hν a eStar gamma R →
      Tendsto (fun n => MethbokeAddon.EhrenfestObstruction.canonicalSlabEnstrophySup
          ν hν a (1 / gamma) n) atTop atTop :=
  @MethbokeAddon.EhrenfestObstruction.stopped_slab_sup_tendsto_atTop

example :
    ∀ (ν : ℝ) (hν : 0 < ν) (a : MethbokeAddon.EhrenfestObstruction.SmoothDatum)
      (eStar gamma : ℝ) (R : ℕ → ℝ),
      MethbokeAddon.EhrenfestObstruction.StoppedForDatum ν hν a eStar gamma R →
      ∀ B : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
        ∃ t ∈ Icc 0 (1 / gamma),
          B ≤ MethbokeAddon.EhrenfestObstruction.canonicalEnstrophy ν hν a n t :=
  @MethbokeAddon.EhrenfestObstruction.stopped_eventually_large_enstrophy

end MethbokeAddon.EhrenfestObstruction.SupremumTypeChecks



#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.scalar_reciprocal_denominator_pos"
#check @MethbokeAddon.EhrenfestObstruction.scalar_reciprocal_denominator_pos
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.scalar_reciprocal_denominator_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.scalar_reciprocal_denominator_pos"
#print axioms MethbokeAddon.EhrenfestObstruction.scalar_reciprocal_denominator_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.scalar_reciprocal_denominator_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_pos"
#check @MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_pos
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_pos"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_pos"
#print axioms MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_pos
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_pos"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_strict_iff"
#check @MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_strict_iff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_strict_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_strict_iff"
#print axioms MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_strict_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_strict_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_weak_iff"
#check @MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_weak_iff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_weak_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_weak_iff"
#print axioms MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_weak_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_weak_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_eq_iff"
#check @MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_eq_iff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_eq_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_eq_iff"
#print axioms MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_eq_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.reciprocal_threshold_eq_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_strict_iff"
#check @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_strict_iff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_strict_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_strict_iff"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_strict_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_strict_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_weak_iff"
#check @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_weak_iff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_weak_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_weak_iff"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_weak_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_weak_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_eq_iff"
#check @MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_eq_iff
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_eq_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_eq_iff"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_eq_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_reciprocal_threshold_eq_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_stopped_exact_threshold_hitting"
#check @MethbokeAddon.EhrenfestObstruction.canonical_stopped_exact_threshold_hitting
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_stopped_exact_threshold_hitting"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_stopped_exact_threshold_hitting"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_stopped_exact_threshold_hitting
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_stopped_exact_threshold_hitting"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_stopped_threshold_crossing"
#check @MethbokeAddon.EhrenfestObstruction.canonical_stopped_threshold_crossing
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_stopped_threshold_crossing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_stopped_threshold_crossing"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_stopped_threshold_crossing
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_stopped_threshold_crossing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_threshold_escape"
#check @MethbokeAddon.EhrenfestObstruction.stopped_threshold_escape
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.stopped_threshold_escape"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_threshold_escape"
#print axioms MethbokeAddon.EhrenfestObstruction.stopped_threshold_escape
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.stopped_threshold_escape"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Ici"
#check @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Ici
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Ici"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Ici"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Ici
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Ici"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Icc"
#check @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_continuousOn_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_bddAbove_Icc"
#check @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_bddAbove_Icc
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_bddAbove_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_bddAbove_Icc"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_bddAbove_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_bddAbove_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_slab_enstrophy_sup_attained"
#check @MethbokeAddon.EhrenfestObstruction.canonical_slab_enstrophy_sup_attained
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_slab_enstrophy_sup_attained"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_slab_enstrophy_sup_attained"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_slab_enstrophy_sup_attained
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_slab_enstrophy_sup_attained"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_slab_sup"
#check @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_slab_sup
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_slab_sup"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_slab_sup"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_slab_sup
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_slab_sup"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_threshold_le_slab_sup"
#check @MethbokeAddon.EhrenfestObstruction.stopped_threshold_le_slab_sup
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.stopped_threshold_le_slab_sup"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_threshold_le_slab_sup"
#print axioms MethbokeAddon.EhrenfestObstruction.stopped_threshold_le_slab_sup
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.stopped_threshold_le_slab_sup"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_slab_sup_tendsto_atTop"
#check @MethbokeAddon.EhrenfestObstruction.stopped_slab_sup_tendsto_atTop
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.stopped_slab_sup_tendsto_atTop"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_slab_sup_tendsto_atTop"
#print axioms MethbokeAddon.EhrenfestObstruction.stopped_slab_sup_tendsto_atTop
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.stopped_slab_sup_tendsto_atTop"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_eventually_large_enstrophy"
#check @MethbokeAddon.EhrenfestObstruction.stopped_eventually_large_enstrophy
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.stopped_eventually_large_enstrophy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.stopped_eventually_large_enstrophy"
#print axioms MethbokeAddon.EhrenfestObstruction.stopped_eventually_large_enstrophy
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.stopped_eventually_large_enstrophy"

