import MethbokeAddon.EhrenfestObstruction.StoppedFamily
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Finite canonical slab suprema and divergence under stopped drift

Every fixed Galerkin trajectory has continuous enstrophy on a closed
nonnegative time slab. Its real supremum is therefore finite and attained.
The original stopped premise forces these actual suprema to tend to infinity
as the cutoff index tends to infinity.
-/

set_option autoImplicit false

open Set Filter SingularClosure

namespace MethbokeAddon.EhrenfestObstruction

theorem canonical_enstrophy_continuousOn_Ici
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (n : ℕ) :
    ContinuousOn (canonicalEnstrophy ν hν a n) (Ici 0) := by
  intro t ht
  change ContinuousWithinAt
    (fun s : ℝ => coefficientDissipation (n + 1)
      ((canonicalFamily ν hν a n).coeff s) / 2) (Ici 0) t
  exact (((canonicalFamily ν hν a n).coefficientEnstrophy_identity ht).div_const 2).continuousWithinAt

theorem canonical_enstrophy_continuousOn_Icc
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (n : ℕ) (T : ℝ) :
    ContinuousOn (canonicalEnstrophy ν hν a n) (Icc 0 T) :=
  (canonical_enstrophy_continuousOn_Ici ν hν a n).mono (fun _ ht => ht.1)

/-- The actual closed-slab supremum, not an assumed uniform bound. -/
noncomputable def canonicalSlabEnstrophySup
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (T : ℝ) (n : ℕ) : ℝ :=
  sSup (canonicalEnstrophy ν hν a n '' Icc 0 T)

/-- Each finite-cutoff enstrophy image is bounded above by compactness. -/
theorem canonical_enstrophy_bddAbove_Icc
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (n : ℕ) (T : ℝ) :
    BddAbove (canonicalEnstrophy ν hν a n '' Icc 0 T) :=
  isCompact_Icc.bddAbove_image (canonical_enstrophy_continuousOn_Icc ν hν a n T)

/-- On a nonempty slab the real supremum is a value of the actual trajectory. -/
theorem canonical_slab_enstrophy_sup_attained
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (T : ℝ) (n : ℕ)
    (hT : 0 ≤ T) :
    ∃ t ∈ Icc 0 T,
      canonicalSlabEnstrophySup ν hν a T n = canonicalEnstrophy ν hν a n t := by
  have hnonempty : (Icc (0 : ℝ) T).Nonempty := ⟨0, ⟨le_rfl, hT⟩⟩
  exact isCompact_Icc.exists_sSup_image_eq hnonempty
    (canonical_enstrophy_continuousOn_Icc ν hν a n T)

/-- Every actual slab value is bounded by its genuine conditional supremum. -/
theorem canonical_enstrophy_le_slab_sup
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (T : ℝ) (n : ℕ)
    (t : ℝ) (ht : t ∈ Icc 0 T) :
    canonicalEnstrophy ν hν a n t ≤ canonicalSlabEnstrophySup ν hν a T n := by
  exact le_csSup (canonical_enstrophy_bddAbove_Icc ν hν a n T)
    (mem_image_of_mem (canonicalEnstrophy ν hν a n) ht)

theorem stopped_threshold_le_slab_sup
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ)
    (hStopped : StoppedForDatum ν hν a eStar gamma R) :
    ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      R n ≤ canonicalSlabEnstrophySup ν hν a (1 / gamma) n := by
  obtain ⟨n₀, hcross⟩ :=
    stopped_threshold_escape ν hν a eStar gamma R hStopped
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨t, ht, hRt⟩ := hcross n hn
  exact hRt.trans (canonical_enstrophy_le_slab_sup
    ν hν a (1 / gamma) n t ⟨ht.1, ht.2.le⟩)

/-- The actual finite closed-slab suprema diverge along the canonical cutoffs. -/
theorem stopped_slab_sup_tendsto_atTop
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ)
    (hStopped : StoppedForDatum ν hν a eStar gamma R) :
    Tendsto (fun n => canonicalSlabEnstrophySup ν hν a (1 / gamma) n)
      atTop atTop := by
  obtain ⟨n₀, hsup⟩ :=
    stopped_threshold_le_slab_sup ν hν a eStar gamma R hStopped
  have hRtop : Tendsto R atTop atTop := hStopped.2.2.2.1
  refine tendsto_atTop_atTop.mpr ?_
  intro B
  obtain ⟨nB, hB⟩ := tendsto_atTop_atTop.mp hRtop B
  refine ⟨max n₀ nB, ?_⟩
  intro n hn
  exact (hB n ((le_max_right n₀ nB).trans hn)).trans
    (hsup n ((le_max_left n₀ nB).trans hn))

/-- An explicit pointwise form of divergence, with a witness for every
sufficiently large cutoff and every requested finite level. -/
theorem stopped_eventually_large_enstrophy
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ)
    (hStopped : StoppedForDatum ν hν a eStar gamma R) :
    ∀ B : ℝ, ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ t ∈ Icc 0 (1 / gamma), B ≤ canonicalEnstrophy ν hν a n t := by
  intro B
  obtain ⟨n₀, hlarge⟩ := tendsto_atTop_atTop.mp
    (stopped_slab_sup_tendsto_atTop ν hν a eStar gamma R hStopped) B
  refine ⟨n₀, ?_⟩
  intro n hn
  have hgamma : 0 < gamma := hStopped.2.1
  obtain ⟨t, ht, hatt⟩ := canonical_slab_enstrophy_sup_attained
    ν hν a (1 / gamma) n (div_pos zero_lt_one hgamma).le
  refine ⟨t, ht, ?_⟩
  rw [← hatt]
  exact hlarge n hn

end MethbokeAddon.EhrenfestObstruction

