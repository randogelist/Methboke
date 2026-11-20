import MethbokeAddon.FDSNR3.Contracts
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# Actual slice jets and weighted parameter smallness in Schwartz space

The recursively constructed slice jets are genuine Schwartz maps on the
full parameter-space product. Their pointwise values are proved equal to
the actual iterated derivatives of the fixed-parameter slice. A global
Schwartz bound on one more parameter derivative then gives weighted
O(parameter) estimates on all of space, without spatial compactness.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped BigOperators ContDiff SchwartzMap
open LineDeriv

namespace MethbokeAddon.FDSNR3

noncomputable section

section General

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def familySpatialInclusion : E →L[ℝ] (ℝ × E) :=
  (0 : E →L[ℝ] ℝ).prod (ContinuousLinearMap.id ℝ E)

@[simp] theorem familySpatialInclusion_apply (z : E) :
    familySpatialInclusion z = ((0 : ℝ), z) := rfl

/-- Full product-space Schwartz representatives of the slice derivatives. -/
def schwartzSliceJet (G : 𝓢(ℝ × E, F)) :
    (n : ℕ) → 𝓢(ℝ × E, ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)
  | 0 => SchwartzMap.postcompCLM
      (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearMap G
  | n + 1 => SchwartzMap.postcompCLM
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => E) F)
        .symm.toContinuousLinearMap
      (SchwartzMap.postcompCLM
        ((ContinuousLinearMap.compL ℝ E (ℝ × E)
          (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F)).flip familySpatialInclusion)
        (SchwartzMap.fderivCLM ℝ (ℝ × E)
          (ContinuousMultilinearMap ℝ (fun _ : Fin n => E) F) (schwartzSliceJet G n)))

theorem schwartzSliceJet_apply (G : 𝓢(ℝ × E, F)) (n : ℕ) (q : ℝ × E) :
    schwartzSliceJet G n q =
      iteratedFDeriv ℝ n (fun z : E => G (q.1, z)) q.2 := by
  induction n generalizing q with
  | zero =>
      simp only [schwartzSliceJet, SchwartzMap.postcompCLM_apply,
        iteratedFDeriv_zero_eq_comp, Function.comp_def]
  | succ n ih =>
      change (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) F).symm
          ((fderiv ℝ (schwartzSliceJet G n : ℝ × E → _) q).comp familySpatialInclusion) = _
      rw [iteratedFDeriv_succ_eq_comp_left]
      apply congrArg (continuousMultilinearCurryLeftEquiv ℝ
        (fun _ : Fin (n + 1) => E) F).symm
      have hmap : HasFDerivAt (fun z : E => (q.1, z)) familySpatialInclusion q.2 := by
        simpa only [familySpatialInclusion] using
          (hasFDerivAt_const q.1 q.2).prodMk (hasFDerivAt_id q.2)
      have hd := ((schwartzSliceJet G n).hasFDerivAt q).comp q.2 hmap
      have heq : (fun z : E => schwartzSliceJet G n (q.1, z)) =
          (fun z : E => iteratedFDeriv ℝ n (fun y : E => G (q.1, y)) z) := by
        funext z
        exact ih (q := (q.1, z))
      simpa only [Function.comp_def, heq] using hd.fderiv.symm

theorem schwartz_weighted_value_bound (G : 𝓢(ℝ × E, F)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, ∀ z : E,
      (1 + ‖z‖) ^ N * ‖G (lam, z)‖ ≤ C := by
  let C : ℝ := 2 ^ N * (Finset.Iic (N, 0)).sup
    (fun m : ℕ × ℕ => SchwartzMap.seminorm ℝ m.1 m.2) G
  refine ⟨C, by dsimp [C]; positivity, ?_⟩
  intro lam z
  have h := G.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
    (m := (N, 0)) le_rfl le_rfl (lam, z)
  have hweight : (1 + ‖z‖) ^ N ≤ (1 + ‖(lam, z)‖) ^ N := by
    gcongr
    exact norm_snd_le (lam, z)
  exact (mul_le_mul_of_nonneg_right hweight (norm_nonneg _)).trans
    (by simpa only [norm_iteratedFDeriv_zero] using h)

/-- Weighted mean-value estimate with a genuine Schwartz derivative bound,
valid for every real parameter. -/
theorem schwartz_weighted_value_linear_bound
    (G : 𝓢(ℝ × E, F)) (hzero : ∀ z : E, G (0, z) = 0) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, ∀ z : E,
      (1 + ‖z‖) ^ N * ‖G (lam, z)‖ ≤ C * |lam| := by
  let D : 𝓢(ℝ × E, F) := ∂_{((1 : ℝ), (0 : E))} G
  obtain ⟨C, hC, hbound⟩ := schwartz_weighted_value_bound D N
  refine ⟨C, hC, ?_⟩
  intro lam z
  let w : ℝ := (1 + ‖z‖) ^ N
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have hd (l : ℝ) : HasDerivAt (fun r : ℝ => w • G (r, z))
      (w • D (l, z)) l := by
    have hmap : HasDerivAt (fun r : ℝ => (r, z)) ((1 : ℝ), (0 : E)) l :=
      (hasDerivAt_id l).prodMk (hasDerivAt_const l z)
    have h := (G.hasFDerivAt (l, z)).comp_hasDerivAt l hmap
    simpa only [D, SchwartzMap.lineDerivOp_apply_eq_fderiv] using h.const_smul w
  have hb : ∀ l ∈ (univ : Set ℝ), ‖w • D (l, z)‖ ≤ C := by
    intro l _
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg hw, w] using hbound l z
  have h := (convex_univ : Convex ℝ (univ : Set ℝ))
    .norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun l _ => (hd l).hasDerivWithinAt) hb (mem_univ (0 : ℝ)) (mem_univ lam)
  simpa only [hzero z, smul_zero, sub_zero, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg hw, w] using h

theorem schwartz_weighted_sliceJet_linear_bound
    (G : 𝓢(ℝ × E, F)) (hzero : ∀ z : E, G (0, z) = 0) (N n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, ∀ z : E,
      (1 + ‖z‖) ^ N *
        ‖iteratedFDeriv ℝ n (fun y : E => G (lam, y)) z‖ ≤ C * |lam| := by
  have hjetzero : ∀ z : E, schwartzSliceJet G n (0, z) = 0 := by
    intro z
    rw [schwartzSliceJet_apply]
    have hf : (fun y : E => G (0, y)) = (fun _ : E => (0 : F)) := funext hzero
    rw [hf]
    simp
  obtain ⟨C, hC, hb⟩ := schwartz_weighted_value_linear_bound
    (schwartzSliceJet G n) hjetzero N
  exact ⟨C, hC, fun lam z => by simpa only [schwartzSliceJet_apply] using hb lam z⟩

theorem schwartz_weighted_finite_sliceJet_linear_bound
    (G : 𝓢(ℝ × E, F)) (hzero : ∀ z : E, G (0, z) = 0) (N r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, ∀ n : ℕ, n ≤ r → ∀ z : E,
      (1 + ‖z‖) ^ N *
        ‖iteratedFDeriv ℝ n (fun y : E => G (lam, y)) z‖ ≤ C * |lam| := by
  classical
  have hf : ∀ j : Fin (r + 1), ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, ∀ z : E,
      (1 + ‖z‖) ^ N *
        ‖iteratedFDeriv ℝ (j : ℕ) (fun y : E => G (lam, y)) z‖ ≤ C * |lam| :=
    fun j => schwartz_weighted_sliceJet_linear_bound G hzero N j
  choose C hC hb using hf
  refine ⟨∑ j : Fin (r + 1), C j, Finset.sum_nonneg (fun j _ => hC j), ?_⟩
  intro lam n hn z
  let j : Fin (r + 1) := ⟨n, Nat.lt_succ_of_le hn⟩
  have hj : C j ≤ ∑ k : Fin (r + 1), C k :=
    Finset.single_le_sum (fun k _ => hC k) (Finset.mem_univ j)
  exact (hb j lam z).trans (mul_le_mul_of_nonneg_right hj (abs_nonneg lam))

end General

/-- Two actual whole-joint Schwartz corrections, both zero at parameter
zero, supply the literal all-weight/all-order FDSN_R3 smallness clause. -/
theorem weightedSmoothSmallness_of_schwartz_corrections
    (ε : ℝ) (u F : Velocity) (U G : ℝ → Velocity)
    (H J : 𝓢(ℝ × (ℝ × Vec), Vec))
    (hH : ∀ lam : ℝ, ∀ z : ℝ × Vec, H (lam, z) = (U lam - u) z.1 z.2)
    (hJ : ∀ lam : ℝ, ∀ z : ℝ × Vec, J (lam, z) = (G lam - F) z.1 z.2)
    (hH0 : ∀ z : ℝ × Vec, H (0, z) = 0)
    (hJ0 : ∀ z : ℝ × Vec, J (0, z) = 0) :
    WeightedSmoothSmallness ε u F U G := by
  intro N r
  obtain ⟨A, hA, hAb⟩ := schwartz_weighted_finite_sliceJet_linear_bound H hH0 N r
  obtain ⟨B, hB, hBb⟩ := schwartz_weighted_finite_sliceJet_linear_bound J hJ0 N r
  refine ⟨A + B, add_nonneg hA hB, ?_⟩
  intro lam _ n hn z
  have hw : (1 + ‖z.2‖) ^ N ≤ (1 + ‖z‖) ^ N := by
    gcongr
    exact norm_snd_le z
  have hHeq : (fun y : ℝ × Vec => (U lam - u) y.1 y.2) =
      (fun y : ℝ × Vec => H (lam, y)) := (funext (hH lam)).symm
  have hJeq : (fun y : ℝ × Vec => (G lam - F) y.1 y.2) =
      (fun y : ℝ × Vec => J (lam, y)) := (funext (hJ lam)).symm
  unfold weightedJet
  rw [hHeq, hJeq]
  calc
    _ ≤ (1 + ‖z‖) ^ N *
          ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => H (lam, y)) z‖ +
        (1 + ‖z‖) ^ N *
          ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => J (lam, y)) z‖ :=
      add_le_add (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
        (mul_le_mul_of_nonneg_right hw (norm_nonneg _))
    _ ≤ A * |lam| + B * |lam| := add_le_add (hAb lam n hn z) (hBb lam n hn z)
    _ = (A + B) * |lam| := by ring

end

end MethbokeAddon.FDSNR3
