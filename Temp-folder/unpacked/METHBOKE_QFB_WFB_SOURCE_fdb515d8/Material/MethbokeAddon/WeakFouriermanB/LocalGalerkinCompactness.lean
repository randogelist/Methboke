import MethbokeAddon.WeakFouriermanB.LocalGalerkinRegularity
import SingularClosure.SobolevArzelaAscoli

/-!
Actual finite-window compactness from a uniform local H2 time integral.
Smooth-data higher bounds and the genuine Galerkin time modulus feed the
proved compact Sobolev inclusion and Arzela--Ascoli. No limit, compactness
certificate, global budget, or physical solution is an input.
Prepared source; matching external verification remains required.
-/

set_option autoImplicit false

open Set MeasureTheory Filter Metric SingularClosure
open scoped Topology BoundedContinuousFunction Interval

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

local instance localCompactTimeInterval (T : ℝ) : CompactSpace (Icc (0 : ℝ) T) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

theorem local_canonical_galerkin_H0_uniform_subsequence
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S) :
    ∃ u : C(Icc (0 : ℝ) T, TorusSobolev 0), ∃ φ : ℕ → ℕ,
      StrictMono φ ∧ TendstoUniformly
        (fun n (t : Icc (0 : ℝ) T) =>
          (canonicalGalerkinSolution ν hν a ha (φ n + 1)).sobolevState 0 t.val)
        u atTop := by
  obtain ⟨B, hB, hbound⟩ := local_galerkin_high_order_pointwise ν hν a ha T hT S hS hH2 1
  obtain ⟨M, hM, hmod⟩ := local_galerkin_high_order_time_modulus ν hν a ha T hT S hS hH2 0
  let F : ℕ → (Icc (0 : ℝ) T) →ᵇ TorusSobolev 0 :=
    canonicalSobolevCurveBounded ν hν a ha T
  let K : Set (TorusSobolev 0) := closure ((torusSobolevInclusion 0) ''
    closedBall (0 : TorusSobolev 1) (B + 1))
  have hK : IsCompact K :=
    (torusSobolevInclusion_compact 0).isCompact_closure_image_closedBall (B + 1)
  have hrange (n : ℕ) (t : Icc (0 : ℝ) T) : F n t ∈ K := by
    apply subset_closure
    refine ⟨(canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 1 t.val, ?_, ?_⟩
    · rw [mem_closedBall, dist_zero_right]
      have hb := (hbound (n + 1) (by omega)
        (canonicalGalerkinSolution ν hν a ha (n + 1))) t.val t.property
      nlinarith [sq_nonneg
        (‖(canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 1 t.val‖ - 1)]
    · exact (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState_inclusion 0 t.val
  have huni : UniformEquicontinuous (fun n (t : Icc (0 : ℝ) T) => F n t) := by
    rw [Metric.uniformEquicontinuous_iff]
    intro ε hε
    refine ⟨ε ^ 2 / (M + 1), div_pos (sq_pos_of_pos hε) (by linarith), ?_⟩
    intro x y hxy n
    change dist (x.val : ℝ) y.val < ε ^ 2 / (M + 1) at hxy
    rw [Real.dist_eq] at hxy
    have hsmall : (M + 1) * |x.val - y.val| < ε ^ 2 := by
      have h := (lt_div_iff₀ (by linarith : 0 < M + 1)).mp hxy
      simpa only [mul_comm] using h
    have hb := hmod (n + 1) (by omega)
      (canonicalGalerkinSolution ν hν a ha (n + 1)) y.val y.property x.val x.property
    rw [dist_eq_norm]
    change ‖(canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 0 x.val -
      (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 0 y.val‖ < ε
    nlinarith [abs_nonneg (x.val - y.val), norm_nonneg
      ((canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 0 x.val -
        (canonicalGalerkinSolution ν hν a ha (n + 1)).sobolevState 0 y.val)]
  have hequi : Equicontinuous ((↑) : (Set.range F) → (Icc (0 : ℝ) T) → TorusSobolev 0) := by
    have he : ((↑) : (Set.range F) → (Icc (0 : ℝ) T) → TorusSobolev 0) =
        (fun f : Set.range F => fun t => F f.property.choose t) := by
      funext f t
      exact congrArg (fun q : (Icc (0 : ℝ) T) →ᵇ TorusSobolev 0 => q t)
        f.property.choose_spec.symm
    rw [he]
    exact huni.equicontinuous.comp (fun f : Set.range F => f.property.choose)
  have hcompact : IsCompact (closure (Set.range F)) :=
    BoundedContinuousFunction.arzela_ascoli K hK (Set.range F)
      (by intro f t hf; obtain ⟨n, rfl⟩ := hf; exact hrange n t) hequi
  obtain ⟨u, _, φ, hφ, hconv⟩ := hcompact.tendsto_subseq
    (fun n => subset_closure (Set.mem_range_self n))
  refine ⟨u.toContinuousMap, φ, hφ, ?_⟩
  change TendstoUniformly (fun n t => F (φ n) t) (fun t => u t) atTop
  simpa only [Function.comp_def] using
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hconv)


end
end MethbokeAddon.WeakFouriermanB
