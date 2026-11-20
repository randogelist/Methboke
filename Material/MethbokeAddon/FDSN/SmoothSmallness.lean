import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Choose

/-!
# Uniform smallness of a smooth parameter family

The spatial derivative here is the actual `iteratedFDeriv` of the fixed-parameter
slice. In applications `E = ℝ × Vec`, so it includes all time-space derivatives
while leaving the family parameter fixed. Every bound is derived from joint
smoothness and compactness; no derivative-bound hypothesis is introduced.
-/

set_option autoImplicit false

noncomputable section

open Set
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Every actual spatial derivative of a smooth parameter family remains
jointly smooth in its parameter and spatial point. -/
theorem contDiff_spatial_iteratedFDeriv
    (G : ℝ × E → F) (hG : ContDiff ℝ ∞ G) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × E =>
      iteratedFDeriv ℝ n (fun z : E => G (p.1, z)) p.2) := by
  induction n with
  | zero =>
      simpa only [iteratedFDeriv_zero_eq_comp, Function.comp_def] using
        (continuousMultilinearCurryFin0 ℝ E F).symm.contDiff.comp hG
  | succ n ih =>
      have haux : ContDiff ℝ ∞ (fun q : (ℝ × E) × E =>
          iteratedFDeriv ℝ n (fun z : E => G (q.1.1, z)) q.2) :=
        ih.comp (contDiff_fst.fst.prodMk contDiff_snd)
      have hd : ContDiff ℝ ∞ (fun p : ℝ × E =>
          fderiv ℝ (fun z : E =>
            iteratedFDeriv ℝ n (fun y : E => G (p.1, y)) z) p.2) :=
        haux.fderiv contDiff_snd (by simp)
      simpa only [iteratedFDeriv_succ_eq_comp_left, Function.comp_def] using
        (continuousMultilinearCurryLeftEquiv ℝ
          (fun _ : Fin (n + 1) => E) F).symm.contDiff.comp hd

/-- Compactness bounds the parameter derivative, and the mean value inequality
then gives a uniform linear bound in the parameter. -/
theorem smooth_family_uniform_linear_bound
    (G : ℝ × E → F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ z : E, G (0, z) = 0)
    (K : Set E) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      ∀ z ∈ K, ‖G (lambda, z)‖ ≤ C * ‖lambda‖ := by
  have haux : ContDiff ℝ ∞ (fun q : (ℝ × E) × ℝ => G (q.2, q.1.2)) :=
    hG.comp (contDiff_snd.prodMk contDiff_fst.snd)
  have hd : ContDiff ℝ ∞ (fun p : ℝ × E =>
      fderiv ℝ (fun lambda : ℝ => G (lambda, p.2)) p.1) :=
    haux.fderiv contDiff_fst (by simp)
  have hcompact : IsCompact (Icc (-1 : ℝ) 1 ×ˢ K) := isCompact_Icc.prod hK
  obtain ⟨B, hB⟩ := hcompact.exists_bound_of_continuousOn hd.continuous.continuousOn
  refine ⟨max B 0, le_max_right _ _, ?_⟩
  intro lambda hlambda z hz
  have hlam : lambda ∈ Icc (-1 : ℝ) 1 := by
    simpa only [mem_Icc, Real.norm_eq_abs, abs_le] using hlambda
  have hsmooth : ContDiff ℝ ∞ (fun l : ℝ => G (l, z)) :=
    hG.comp (contDiff_id.prodMk contDiff_const)
  have hbound : ∀ l ∈ Icc (-1 : ℝ) 1,
      ‖fderiv ℝ (fun u : ℝ => G (u, z)) l‖ ≤ max B 0 := by
    intro l hl
    exact (hB (l, z) ⟨hl, hz⟩).trans (le_max_left _ _)
  have hmvt := (convex_Icc (-1 : ℝ) 1).norm_image_sub_le_of_norm_fderiv_le
    (fun l _ => (hsmooth.differentiable (by simp)) l) hbound
    (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 from ⟨neg_nonpos.mpr zero_le_one, zero_le_one⟩)
    hlam
  simpa only [hzero z, sub_zero] using hmvt

/-- The `n`-th spatial derivative is uniformly linear in the parameter. -/
theorem smooth_family_iteratedFDeriv_linear_bound
    (G : ℝ × E → F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ z : E, G (0, z) = 0)
    (K : Set E) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      ∀ z ∈ K,
        ‖iteratedFDeriv ℝ n (fun y : E => G (lambda, y)) z‖ ≤ C * ‖lambda‖ := by
  apply smooth_family_uniform_linear_bound
    (fun p : ℝ × E => iteratedFDeriv ℝ n (fun z : E => G (p.1, z)) p.2)
    (contDiff_spatial_iteratedFDeriv G hG n) _ K hK
  intro z
  have hfun : (fun y : E => G (0, y)) = fun _ : E => (0 : F) := funext hzero
  rw [hfun]
  simp

/-- A single constant controls every derivative through a prescribed finite
order on a prescribed compact set. The parameter radius is the explicit `1`.
-/
theorem smooth_family_finite_order_linear_bound
    (G : ℝ × E → F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ z : E, G (0, z) = 0)
    (K : Set E) (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      ∀ n : ℕ, n ≤ r → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ n (fun y : E => G (lambda, y)) z‖ ≤ C * ‖lambda‖ := by
  classical
  have hfinite : ∀ j : Fin (r + 1), ∃ C : ℝ, 0 ≤ C ∧
      ∀ lambda : ℝ, ‖lambda‖ ≤ 1 → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ (j : ℕ) (fun y : E => G (lambda, y)) z‖ ≤ C * ‖lambda‖ :=
    fun j => smooth_family_iteratedFDeriv_linear_bound G hG hzero K hK j
  choose C hC hbound using hfinite
  refine ⟨∑ j : Fin (r + 1), C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro lambda hlambda n hn z hz
  let j : Fin (r + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hj : C j ≤ ∑ k : Fin (r + 1), C k :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ j)
  exact (hbound j lambda hlambda z hz).trans
    (mul_le_mul_of_nonneg_right hj (norm_nonneg lambda))

end MethbokeAddon.FDSN
