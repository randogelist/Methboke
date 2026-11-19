import MethbokeAddon.EhrenfestObstruction.SlabDescent
import Mathlib.Topology.Order.IntermediateValue

/-!
# A scalar lower-level hit under a pre-hit derivative bound

The rate hypothesis is imposed only while the whole preceding history stays
strictly above the target level, and only before the horizon 1 / gamma.
The proof constructs a hit; it assumes no first-hit time.
-/

namespace MethbokeAddon.EhrenfestObstruction

open Set

/-- A guarded negative derivative forces the scalar function below the target
level by the explicit deadline. -/
theorem stopped_scalar_le_by_deadline
    (v rate : ℝ → ℝ) (gamma r : ℝ)
    (hgamma : 0 < gamma) (hr : 0 < r)
    (hr0 : r < v 0) (hv0 : v 0 ≤ 1)
    (hcont : ContinuousOn v (Icc 0 (1 / gamma)))
    (hderiv : ∀ t, 0 ≤ t → t < 1 / gamma →
      (∀ s, 0 ≤ s → s ≤ t → r < v s) →
      HasDerivWithinAt v (rate t) (Ici 0) t ∧ rate t ≤ -gamma) :
    ∃ t ∈ Icc 0 ((v 0 - r) / gamma), v t ≤ r := by
  classical
  let d : ℝ := (v 0 - r) / gamma
  have hdpos : 0 < d := div_pos (sub_pos.mpr hr0) hgamma
  have hdT : d < 1 / gamma := by
    exact div_lt_div_of_pos_right (by linarith : v 0 - r < 1) hgamma
  have hcontd : ContinuousOn v (Icc 0 d) :=
    hcont.mono (fun x hx => ⟨hx.1, hx.2.trans hdT.le⟩)
  change ∃ t ∈ Icc 0 d, v t ≤ r
  by_contra hno
  have hlower : ∀ s ∈ Icc 0 d, r < v s := by
    intro s hs
    by_contra hnot
    exact hno ⟨s, hs, le_of_not_gt hnot⟩
  have hint : ∀ t ∈ Ioo 0 d,
      HasDerivAt v (rate t) t ∧ rate t ≤ -gamma := by
    intro t ht
    have hhistory : ∀ s, 0 ≤ s → s ≤ t → r < v s := by
      intro s hs0 hst
      exact hlower s ⟨hs0, hst.trans ht.2.le⟩
    obtain ⟨hdt, hrate⟩ :=
      hderiv t ht.1.le (ht.2.trans hdT) hhistory
    have hdt_slab : HasDerivWithinAt v (rate t) (Icc 0 d) t :=
      hdt.mono (fun x hx => hx.1)
    exact ⟨hdt_slab.hasDerivAt (Icc_mem_nhds ht.1 ht.2), hrate⟩
  have hterminal :=
    terminal_le_of_rate_le v rate d gamma hdpos hcontd
      (fun t ht => (hint t ht).1) (fun t ht => (hint t ht).2)
  have hmul : gamma * d = v 0 - r := by
    dsimp [d]
    rw [mul_comm]
    exact div_mul_cancel₀ _ hgamma.ne'
  rw [hmul] at hterminal
  have hstrict := hlower d ⟨hdpos.le, le_rfl⟩
  linarith

/-- The guarded derivative bound forces an exact hit of the target level by
the explicit deadline. Continuity turns the lower-level witness into equality. -/
theorem stopped_scalar_hitting
    (v rate : ℝ → ℝ) (gamma r : ℝ)
    (hgamma : 0 < gamma) (hr : 0 < r)
    (hr0 : r < v 0) (hv0 : v 0 ≤ 1)
    (hcont : ContinuousOn v (Icc 0 (1 / gamma)))
    (hderiv : ∀ t, 0 ≤ t → t < 1 / gamma →
      (∀ s, 0 ≤ s → s ≤ t → r < v s) →
      HasDerivWithinAt v (rate t) (Ici 0) t ∧ rate t ≤ -gamma) :
    ∃ t ∈ Icc 0 ((v 0 - r) / gamma), v t = r := by
  obtain ⟨s, hs, hsr⟩ :=
    stopped_scalar_le_by_deadline v rate gamma r hgamma hr hr0 hv0 hcont hderiv
  have hdeadline : (v 0 - r) / gamma < 1 / gamma :=
    div_lt_div_of_pos_right (by linarith : v 0 - r < 1) hgamma
  have hsT : s ≤ 1 / gamma := hs.2.trans hdeadline.le
  have hconts : ContinuousOn v (Icc 0 s) :=
    hcont.mono (fun x hx => ⟨hx.1, hx.2.trans hsT⟩)
  obtain ⟨t, ht, htr⟩ :=
    intermediate_value_Icc' hs.1 hconts
      (show r ∈ Icc (v s) (v 0) from ⟨hsr, hr0.le⟩)
  exact ⟨t, ⟨ht.1, ht.2.trans hs.2⟩, htr⟩

end MethbokeAddon.EhrenfestObstruction

