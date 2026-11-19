import MethbokeAddon.EhrenfestObstruction.ReciprocalDrift
import MethbokeAddon.EhrenfestObstruction.ReciprocalThreshold
import MethbokeAddon.EhrenfestObstruction.StoppedScalar

/-!
# Canonical threshold crossing under the literal stopped bound

For a cutoff already above its threshold, time zero is a crossing witness.
Otherwise the scalar hitting theorem supplies an exact hit before 1/gamma.
No uniform initial-enstrophy estimate is needed for this dichotomy.
-/

set_option autoImplicit false

open Set

namespace MethbokeAddon.EhrenfestObstruction

theorem canonical_reciprocal_threshold_strict_iff
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ) (heStar : 0 < eStar) (n : ℕ) (t R : ℝ) (hR : 0 ≤ R) :
    (1 + R / eStar)⁻¹ < canonicalReciprocal ν hν a eStar n t ↔
      canonicalEnstrophy ν hν a n t < R := by
  change (1 + R / eStar)⁻¹ <
      (1 + canonicalEnstrophy ν hν a n t / eStar)⁻¹ ↔
    canonicalEnstrophy ν hν a n t < R
  exact reciprocal_threshold_strict_iff eStar
    (canonicalEnstrophy ν hν a n t) R heStar
    (canonical_enstrophy_nonneg ν hν a n t) hR

theorem canonical_reciprocal_threshold_weak_iff
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ) (heStar : 0 < eStar) (n : ℕ) (t R : ℝ) (hR : 0 ≤ R) :
    canonicalReciprocal ν hν a eStar n t ≤ (1 + R / eStar)⁻¹ ↔
      R ≤ canonicalEnstrophy ν hν a n t := by
  change (1 + canonicalEnstrophy ν hν a n t / eStar)⁻¹ ≤
      (1 + R / eStar)⁻¹ ↔ R ≤ canonicalEnstrophy ν hν a n t
  exact reciprocal_threshold_weak_iff eStar
    (canonicalEnstrophy ν hν a n t) R heStar
    (canonical_enstrophy_nonneg ν hν a n t) hR

theorem canonical_reciprocal_threshold_eq_iff
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ) (heStar : 0 < eStar) (n : ℕ) (t R : ℝ) (hR : 0 ≤ R) :
    canonicalReciprocal ν hν a eStar n t = (1 + R / eStar)⁻¹ ↔
      canonicalEnstrophy ν hν a n t = R := by
  change (1 + canonicalEnstrophy ν hν a n t / eStar)⁻¹ =
      (1 + R / eStar)⁻¹ ↔ canonicalEnstrophy ν hν a n t = R
  exact reciprocal_threshold_eq_iff eStar
    (canonicalEnstrophy ν hν a n t) R heStar
    (canonical_enstrophy_nonneg ν hν a n t) hR

/-- If the initial enstrophy is strictly below the positive threshold, the
literal stopped bound produces an exact hit strictly before the horizon. -/
theorem canonical_stopped_exact_threshold_hitting
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma R : ℝ) (n : ℕ)
    (heStar : 0 < eStar) (hgamma : 0 < gamma) (hR : 0 < R)
    (hbelow : canonicalEnstrophy ν hν a n 0 < R)
    (hStopped : ∀ t : ℝ,
      PreHit (canonicalEnstrophy ν hν a n) R (1 / gamma) t →
        canonicalDrift ν hν a eStar n t ≤ -gamma) :
    ∃ t ∈ Ico 0 (1 / gamma), canonicalEnstrophy ν hν a n t = R := by
  let v : ℝ → ℝ := canonicalReciprocal ν hν a eStar n
  let rate : ℝ → ℝ := canonicalDrift ν hν a eStar n
  let r : ℝ := (1 + R / eStar)⁻¹
  have hr : 0 < r := reciprocal_threshold_pos eStar R heStar hR.le
  have hr0 : r < v 0 :=
    (canonical_reciprocal_threshold_strict_iff ν hν a eStar heStar n 0 R hR.le).mpr
      hbelow
  have hv0 : v 0 ≤ 1 :=
    (canonical_reciprocal_bounds ν hν a eStar heStar n 0 le_rfl).2
  have hcont : ContinuousOn v (Icc 0 (1 / gamma)) :=
    canonical_reciprocal_continuousOn_Icc ν hν a eStar heStar n (1 / gamma)
  have hderiv : ∀ t, 0 ≤ t → t < 1 / gamma →
      (∀ s, 0 ≤ s → s ≤ t → r < v s) →
      HasDerivWithinAt v (rate t) (Ici 0) t ∧ rate t ≤ -gamma := by
    intro t ht0 htT hhistory
    have hpre : PreHit (canonicalEnstrophy ν hν a n) R (1 / gamma) t := by
      refine ⟨ht0, htT, ?_⟩
      intro s hs0 hst
      exact (canonical_reciprocal_threshold_strict_iff
        ν hν a eStar heStar n s R hR.le).mp (hhistory s hs0 hst)
    exact ⟨canonical_reciprocal_hasDerivWithinAt
      ν hν a eStar heStar n t ht0, hStopped t hpre⟩
  obtain ⟨t, ht, hvt⟩ :=
    stopped_scalar_hitting v rate gamma r hgamma hr hr0 hv0 hcont hderiv
  have hdeadline : (v 0 - r) / gamma < 1 / gamma :=
    div_lt_div_of_pos_right (by linarith : v 0 - r < 1) hgamma
  refine ⟨t, ⟨ht.1, ht.2.trans_lt hdeadline⟩, ?_⟩
  exact (canonical_reciprocal_threshold_eq_iff
    ν hν a eStar heStar n t R hR.le).mp hvt

/-- Each positive threshold is crossed before the horizon: time zero handles
the case where the initial value is already at or above the threshold. -/
theorem canonical_stopped_threshold_crossing
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma R : ℝ) (n : ℕ)
    (heStar : 0 < eStar) (hgamma : 0 < gamma) (hR : 0 < R)
    (hStopped : ∀ t : ℝ,
      PreHit (canonicalEnstrophy ν hν a n) R (1 / gamma) t →
        canonicalDrift ν hν a eStar n t ≤ -gamma) :
    ∃ t ∈ Ico 0 (1 / gamma), R ≤ canonicalEnstrophy ν hν a n t := by
  by_cases hInitial : R ≤ canonicalEnstrophy ν hν a n 0
  · exact ⟨0, ⟨le_rfl, div_pos zero_lt_one hgamma⟩, hInitial⟩
  · obtain ⟨t, ht, hhit⟩ :=
      canonical_stopped_exact_threshold_hitting ν hν a eStar gamma R n
        heStar hgamma hR (lt_of_not_ge hInitial) hStopped
    exact ⟨t, ht, hhit.ge⟩

/-- The original stopped premise gives threshold-crossing witnesses for every
eventually qualifying cutoff. No initial-enstrophy uniformity premise is added. -/
theorem stopped_threshold_escape
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ)
    (hStopped : StoppedForDatum ν hν a eStar gamma R) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ t ∈ Ico 0 (1 / gamma), R n ≤ canonicalEnstrophy ν hν a n t := by
  rcases hStopped with ⟨heStar, hgamma, hR, _hRtop, n₀, hstop⟩
  refine ⟨n₀, ?_⟩
  intro n hn
  exact canonical_stopped_threshold_crossing ν hν a eStar gamma (R n) n
    heStar hgamma (hR n) (hstop n hn)

end MethbokeAddon.EhrenfestObstruction

