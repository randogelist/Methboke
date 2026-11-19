import MethbokeAddon.EhrenfestObstruction.ReciprocalDrift
import MethbokeAddon.EhrenfestObstruction.SlabDescent

/-!
# One-cutoff contradiction for the actual canonical family

An eventual bound on the closed time slab and divergence of the supplied
thresholds make the pre-hit guard hold for one selected cutoff throughout the
open slab. Terminal descent contradicts the positive reciprocal. There is no
first-hit construction or uniform initial-enstrophy hypothesis in this proof.

Candidate source; matching external cached type/axiom verification is pending.
-/

set_option autoImplicit false

open Set Filter SingularClosure

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

theorem stopped_rejects_eventual_slab_bound
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ)
    (hStopped : StoppedForDatum ν hν a eStar gamma R) :
    ¬ (∃ C : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) (1 / gamma),
      canonicalEnstrophy ν hν a n t ≤ C) := by
  rcases hStopped with ⟨heStar, hgamma, _hRpos, hRlim, n₀, hStop⟩
  rintro ⟨C, hBound⟩
  have hLarge : ∀ᶠ n in atTop, C < R n :=
    hRlim.eventually (eventually_gt_atTop C)
  have hIndex : ∀ᶠ n : ℕ in atTop, n₀ ≤ n := eventually_ge_atTop n₀
  obtain ⟨n, hnBound, hnIndex, hnLarge⟩ :=
    (hBound.and (hIndex.and hLarge)).exists
  have hT : 0 < (1 : ℝ) / gamma := div_pos zero_lt_one hgamma
  have hRate : ∀ t ∈ Ioo (0 : ℝ) (1 / gamma),
      canonicalDrift ν hν a eStar n t ≤ -gamma := by
    intro t ht
    apply hStop n hnIndex t
    refine ⟨ht.1.le, ht.2, ?_⟩
    intro s hs hst
    exact (hnBound s ⟨hs, hst.trans ht.2.le⟩).trans_lt hnLarge
  have hDeriv : ∀ t ∈ Ioo (0 : ℝ) (1 / gamma),
      HasDerivAt (canonicalReciprocal ν hν a eStar n)
        (canonicalDrift ν hν a eStar n t) t := by
    intro t ht
    exact canonical_reciprocal_hasDerivAt ν hν a eStar heStar n t ht.1
  have hInitial :=
    (canonical_reciprocal_bounds ν hν a eStar heStar n 0 le_rfl).2
  have hTerminal :=
    (canonical_reciprocal_bounds ν hν a eStar heStar n (1 / gamma) hT.le).1
  have hProduct : gamma * ((1 : ℝ) / gamma) = 1 := by
    field_simp [ne_of_gt hgamma]
  have hBudget : canonicalReciprocal ν hν a eStar n 0 ≤
      gamma * (1 / gamma) := by
    simpa only [hProduct] using hInitial
  exact positive_terminal_contradiction
    (canonicalReciprocal ν hν a eStar n)
    (canonicalDrift ν hν a eStar n)
    (1 / gamma) gamma hT
    (canonical_reciprocal_continuousOn_Icc ν hν a eStar heStar n (1 / gamma))
    hDeriv hRate hBudget hTerminal

end
end MethbokeAddon.EhrenfestObstruction
