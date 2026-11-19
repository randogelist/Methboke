import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
Guarded scalar bootstrap for the actual Galerkin error estimate.

The derivative estimate is required only while the nonnegative error is at
most one. A strict exponential comparison fence proves this guard on the
whole slab, after which the signed Gronwall theorem sharpens the estimate.
The guard is a conclusion, never an input trajectory bound.

Prepared candidate for cached external verification only. No local Lean
execution has been performed.
-/

set_option autoImplicit false

open Set Filter
open scoped Topology

namespace MethbokeAddon.EhrenfestObstruction

noncomputable section

/-- A cubic error term is linear below the unit threshold. -/
theorem cubic_le_self_of_mem_unit_interval
    {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) : x ^ 3 ≤ x := by
  have hsq : x ^ 2 ≤ x := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hx1)]
  have hcube : x ^ 3 ≤ x ^ 2 := by
    nlinarith [mul_nonneg hx (sub_nonneg.mpr hsq)]
  exact hcube.trans hsq

/-- The explicit fence has derivative `(2*C+1)` times its value. -/
theorem small_forcing_fence_hasDerivAt (C epsilon t : ℝ) :
    HasDerivAt (fun s : ℝ => 2 * epsilon * Real.exp ((2 * C + 1) * s))
      ((2 * C + 1) * (2 * epsilon * Real.exp ((2 * C + 1) * t))) t := by
  convert (((hasDerivAt_id t).const_mul (2 * C + 1)).exp.const_mul
    (2 * epsilon)) using 1 <;> (try simp only [id_eq]) <;> ring

/-- A small positive forcing gives a global fence on the chosen compact
slab from a derivative inequality that is only assumed below one.

The stronger, convenient smallness test is sufficient for every forcing
sequence tending to zero on a fixed slab; it avoids constructing a first
exit time. No derivative at the right endpoint is required.
-/
theorem guarded_cubic_small_forcing_bound
    {D d : ℝ → ℝ} {C epsilon T : ℝ}
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hsmall : 2 * epsilon * Real.exp ((2 * C + 1) * T) ≤ 1)
    (hD : ContinuousOn D (Icc 0 T))
    (hinit : D 0 ≤ 0)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt D (d t) (Ici 0) t)
    (hguard : ∀ t ∈ Ico 0 T, D t ≤ 1 →
      d t ≤ C * (D t + (D t) ^ 3) + epsilon) :
    ∀ t ∈ Icc 0 T,
      D t ≤ 2 * epsilon * Real.exp ((2 * C + 1) * t) ∧ D t ≤ 1 := by
  let B : ℝ → ℝ := fun t => 2 * epsilon * Real.exp ((2 * C + 1) * t)
  have hK : 0 ≤ 2 * C + 1 := by linarith
  have hBpos (t : ℝ) : 0 < B t := by
    dsimp [B]
    positivity
  have hBupper : ∀ t ∈ Icc 0 T, B t ≤ 1 := by
    intro t ht
    apply le_trans _ hsmall
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK))
      (by positivity : 0 ≤ 2 * epsilon)
  have hBlower : ∀ t ∈ Icc 0 T, 2 * epsilon ≤ B t := by
    intro t ht
    have hexp : 1 ≤ Real.exp ((2 * C + 1) * t) := by
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (mul_nonneg hK ht.1))
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2 * epsilon))
  have hfence : ∀ t ∈ Icc 0 T, D t ≤ B t := by
    intro t ht
    refine image_le_of_deriv_right_lt_deriv_boundary
      (f' := d) (B := B) (B' := fun r => (2 * C + 1) * B r)
      hD ?_ ?_ ?_ ?_ ht
    · intro r hr
      exact (hderiv r hr).mono (fun s hs => hr.1.trans hs)
    · exact hinit.trans (hBpos 0).le
    · intro r
      exact small_forcing_fence_hasDerivAt C epsilon r
    · intro r hr heq
      have hrcc : r ∈ Icc (0 : ℝ) T := ⟨hr.1, hr.2.le⟩
      have hunit : D r ≤ 1 := by
        rw [heq]
        exact hBupper r hrcc
      have hnonneg : 0 ≤ D r := by
        rw [heq]
        exact (hBpos r).le
      have hcube := cubic_le_self_of_mem_unit_interval hnonneg hunit
      have hlinear : C * (D r + (D r) ^ 3) ≤ 2 * C * D r := by
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hcube)]
      have hrate := hguard r hr hunit
      have hlower := hBlower r hrcc
      rw [heq] at hlinear hrate
      nlinarith
  intro t ht
  exact ⟨hfence t ht, (hfence t ht).trans (hBupper t ht)⟩

/-- Once the guarded estimate closes, the signed Gronwall inequality gives
the usual sharp linear comparison. This bounds the derivative above and
does not incorrectly assume a bound on its absolute value.
-/
theorem guarded_cubic_small_forcing_gronwall
    {D d : ℝ → ℝ} {C epsilon T : ℝ}
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hsmall : 2 * epsilon * Real.exp ((2 * C + 1) * T) ≤ 1)
    (hD : ContinuousOn D (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hinit : D 0 ≤ 0)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt D (d t) (Ici 0) t)
    (hguard : ∀ t ∈ Ico 0 T, D t ≤ 1 →
      d t ≤ C * (D t + (D t) ^ 3) + epsilon) :
    ∀ t ∈ Icc 0 T, D t ≤ gronwallBound 0 (2 * C) epsilon t := by
  have hfence := guarded_cubic_small_forcing_bound
    hC hepsilon hsmall hD hinit hderiv hguard
  have hlinear : ∀ t ∈ Ico 0 T, d t ≤ (2 * C) * D t + epsilon := by
    intro t ht
    have htcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1, ht.2.le⟩
    have hunit := (hfence t htcc).2
    have hcube := cubic_le_self_of_mem_unit_interval (hnonneg t htcc) hunit
    have hrate := hguard t ht hunit
    nlinarith [mul_nonneg hC (sub_nonneg.mpr hcube)]
  have hg := le_gronwallBound_of_liminf_deriv_right_le hD
    (fun t ht _r hr =>
      ((hderiv t ht).mono (fun s hs => ht.1.trans hs)).liminf_right_slope_le hr)
    hinit hlinear
  intro t ht
  simpa only [sub_zero] using hg t ht

/-- On a fixed slab every positive forcing sequence converging to zero
eventually satisfies the explicit smallness test. Thus the cutoff-uniform
unit error bound follows from the differential estimate itself.
-/
theorem eventually_guarded_cubic_unit_bound
    {D d : ℕ → ℝ → ℝ} {epsilon : ℕ → ℝ} {C T : ℝ}
    (hC : 0 ≤ C)
    (hepsilon : ∀ᶠ n in atTop, 0 < epsilon n)
    (hlim : Tendsto epsilon atTop (𝓝 0))
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hinit : ∀ n, D n 0 ≤ 0)
    (hderiv : ∀ n, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (D n) (d n t) (Ici 0) t)
    (hguard : ∀ n, ∀ t ∈ Ico 0 T, D n t ≤ 1 →
      d n t ≤ C * (D n t + (D n t) ^ 3) + epsilon n) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, D n t ≤ 1 := by
  have hscaled : Tendsto
      (fun n => 2 * epsilon n * Real.exp ((2 * C + 1) * T))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_mul] using
      (hlim.const_mul 2).mul_const (Real.exp ((2 * C + 1) * T))
  have hsmall : ∀ᶠ n in atTop,
      2 * epsilon n * Real.exp ((2 * C + 1) * T) < 1 :=
    hscaled.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hepsilon, hsmall] with n hpos hnsmall
  intro t ht
  exact (guarded_cubic_small_forcing_bound hC hpos hnsmall.le
    (hD n) (hinit n) (hderiv n) (hguard n) t ht).2

/-- Interior derivative version of the guarded bootstrap. Continuity and
the strictly positive fence at zero provide a starting point `a` with
`0 < a ≤ t` where `D a < B a`. The comparison on `[a,t]` therefore uses
only derivatives strictly inside the original slab, with no limit of
initial-time derivatives and no first-exit construction.
-/
theorem guarded_cubic_small_forcing_bound_interior
    {D d : ℝ → ℝ} {C epsilon T : ℝ}
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hsmall : 2 * epsilon * Real.exp ((2 * C + 1) * T) ≤ 1)
    (hD : ContinuousOn D (Icc 0 T))
    (hinit : D 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt D (d t) t)
    (hguard : ∀ t ∈ Ioo 0 T, D t ≤ 1 →
      d t ≤ C * (D t + (D t) ^ 3) + epsilon) :
    ∀ t ∈ Icc 0 T,
      D t ≤ 2 * epsilon * Real.exp ((2 * C + 1) * t) ∧ D t ≤ 1 := by
  let B : ℝ → ℝ := fun t => 2 * epsilon * Real.exp ((2 * C + 1) * t)
  have hK : 0 ≤ 2 * C + 1 := by linarith
  have hBpos (t : ℝ) : 0 < B t := by
    dsimp [B]
    positivity
  have hBcont : Continuous B := by
    dsimp [B]
    fun_prop
  have hBupper : ∀ t ∈ Icc 0 T, B t ≤ 1 := by
    intro t ht
    apply le_trans _ hsmall
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht.2 hK))
      (by positivity : 0 ≤ 2 * epsilon)
  have hBlower : ∀ t ∈ Icc 0 T, 2 * epsilon ≤ B t := by
    intro t ht
    have hexp : 1 ≤ Real.exp ((2 * C + 1) * t) := by
      simpa only [Real.exp_zero] using
        (Real.exp_le_exp.mpr (mul_nonneg hK ht.1))
    simpa only [mul_one] using
      (mul_le_mul_of_nonneg_left hexp (by positivity : 0 ≤ 2 * epsilon))
  have hfence : ∀ t ∈ Icc 0 T, D t ≤ B t := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact hinit.trans (hBpos 0).le
    have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
    have hTpos : 0 < T := htpos.trans_le ht.2
    have hpair : ContinuousOn (fun s => (D s, B s)) (Icc 0 T) :=
      hD.prodMk hBcont.continuousOn
    have hnear : ∀ᶠ s in 𝓝[Icc 0 T] (0 : ℝ), D s < B s :=
      hpair 0 ⟨le_rfl, hTpos.le⟩
        (IsOpen.mem_nhds (isOpen_lt continuous_fst continuous_snd)
          (hinit.trans_lt (hBpos 0)))
    have hnearGT : ∀ᶠ s in 𝓝[>] (0 : ℝ), D s < B s :=
      nhdsWithin_le_of_mem (Icc_mem_nhdsGT_of_mem ⟨le_rfl, hTpos⟩) hnear
    obtain ⟨a, haD, ha⟩ := (hnearGT.and (Ioc_mem_nhdsGT htpos)).exists
    refine image_le_of_deriv_right_lt_deriv_boundary
      (f' := d) (B := B) (B' := fun r => (2 * C + 1) * B r)
      (hD.mono (fun s hs => ⟨ha.1.le.trans hs.1, hs.2.trans ht.2⟩))
      ?_ haD.le ?_ ?_ ⟨ha.2, le_rfl⟩
    · intro r hr
      exact (hderiv r ⟨ha.1.trans_le hr.1, hr.2.trans_le ht.2⟩).hasDerivWithinAt
    · intro r
      exact small_forcing_fence_hasDerivAt C epsilon r
    · intro r hr heq
      have hrio : r ∈ Ioo (0 : ℝ) T :=
        ⟨ha.1.trans_le hr.1, hr.2.trans_le ht.2⟩
      have hrcc : r ∈ Icc (0 : ℝ) T := ⟨hrio.1.le, hrio.2.le⟩
      have hunit : D r ≤ 1 := by
        rw [heq]
        exact hBupper r hrcc
      have hnonneg : 0 ≤ D r := by
        rw [heq]
        exact (hBpos r).le
      have hcube := cubic_le_self_of_mem_unit_interval hnonneg hunit
      have hlinear : C * (D r + (D r) ^ 3) ≤ 2 * C * D r := by
        nlinarith [mul_nonneg hC (sub_nonneg.mpr hcube)]
      have hrate := hguard r hrio hunit
      have hlower := hBlower r hrcc
      rw [heq] at hlinear hrate
      nlinarith
  intro t ht
  exact ⟨hfence t ht, (hfence t ht).trans (hBupper t ht)⟩

/-- The eventual unit bound needed by E09, requiring only actual interior
time derivatives and closed-slab continuity of each error trajectory.
-/
theorem eventually_guarded_cubic_unit_bound_interior
    {D d : ℕ → ℝ → ℝ} {epsilon : ℕ → ℝ} {C T : ℝ}
    (hC : 0 ≤ C)
    (hepsilon : ∀ᶠ n in atTop, 0 < epsilon n)
    (hlim : Tendsto epsilon atTop (𝓝 0))
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hinit : ∀ n, D n 0 ≤ 0)
    (hderiv : ∀ n, ∀ t ∈ Ioo 0 T, HasDerivAt (D n) (d n t) t)
    (hguard : ∀ n, ∀ t ∈ Ioo 0 T, D n t ≤ 1 →
      d n t ≤ C * (D n t + (D n t) ^ 3) + epsilon n) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, D n t ≤ 1 := by
  have hscaled : Tendsto
      (fun n => 2 * epsilon n * Real.exp ((2 * C + 1) * T))
      atTop (𝓝 (0 : ℝ)) := by
    simpa only [mul_zero, zero_mul] using
      (hlim.const_mul 2).mul_const (Real.exp ((2 * C + 1) * T))
  have hsmall : ∀ᶠ n in atTop,
      2 * epsilon n * Real.exp ((2 * C + 1) * T) < 1 :=
    hscaled.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hepsilon, hsmall] with n hpos hnsmall
  intro t ht
  exact (guarded_cubic_small_forcing_bound_interior hC hpos hnsmall.le
    (hD n) (hinit n) (hderiv n) (hguard n) t ht).2

end

end MethbokeAddon.EhrenfestObstruction
