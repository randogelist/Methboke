import SingularClosure.HighOrderAccumulation
import SingularClosure.HighOrderTimeModulus

/-!
Finite-window preservation of every Sobolev order for smooth initial data.

The only uniform analytic input is the actual integral of the finite Galerkin
H2 norm on one fixed interval. The high-order estimate and the smooth initial
Fourier bound give all higher orders on that same interval, including time zero.
The interval never shrinks with the requested regularity order. These are
source candidates requiring matching external compiler and axiom evidence.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped Interval

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

theorem local_galerkin_high_order_accumulation
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S)
    (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T,
        ‖g.sobolevState m t‖ ^ 2 +
          ν * (∫ s in (0 : ℝ)..t, ‖g.sobolevState (m + 1) s‖ ^ 2) ≤ B := by
  obtain ⟨C, hC, hineq⟩ := GALERKIN_HIGH_ORDER_DIFFERENTIAL_INEQUALITY m
  let E₀ : ℝ := ‖smoothDatumSobolev m a ha.smooth ha.periodic‖ ^ 2
  let M : ℝ := 2 * ν * T + C / ν * S
  refine ⟨E₀ * Real.exp M, mul_nonneg (sq_nonneg _) (Real.exp_pos _).le, ?_⟩
  intro N hN g
  let y : ℝ → ℝ := fun t => highOrderEnergy m N (g.coeff t)
  let z : ℝ → ℝ := fun t => Real.sqrt (highOrderEnergy (m + 1) N (g.coeff t))
  let d : ℝ → ℝ := fun t => (-2 * ν) *
    (highOrderEnergy (m + 1) N (g.coeff t) - highOrderEnergy m N (g.coeff t)) -
      2 * highOrderNonlinearPower m N (g.coeff t)
  let A : ℝ → ℝ := fun t => 2 * ν + C / ν * highOrderEnergy 2 N (g.coeff t)
  have hy : ContinuousOn y (Icc 0 T) :=
    (g.highOrderEnergy_continuousOn m).mono (fun t ht => ht.1)
  have hz : ContinuousOn z (Icc 0 T) :=
    (Real.continuous_sqrt.comp_continuousOn
      (g.highOrderEnergy_continuousOn (m + 1))).mono (fun t ht => ht.1)
  have hE2 : ContinuousOn (fun t => highOrderEnergy 2 N (g.coeff t)) (Icc 0 T) :=
    (g.highOrderEnergy_continuousOn 2).mono (fun t ht => ht.1)
  have hA : ContinuousOn A (Icc 0 T) :=
    continuousOn_const.add (continuousOn_const.mul hE2)
  have hA_nonneg (t : ℝ) (_ht : t ∈ Icc 0 T) : 0 ≤ A t := by
    exact add_nonneg (mul_nonneg (by norm_num) hν.le)
      (mul_nonneg (div_nonneg hC.le hν.le) (highOrderEnergy_nonneg _ _ _))
  have hderiv (t : ℝ) (ht : t ∈ Ioo 0 T) : HasDerivAt y (d t) t :=
    (g.highOrderEnergy_balance m ht.1.le).hasDerivAt (Ici_mem_nhds ht.1)
  have hlinear (t : ℝ) (ht : t ∈ Ioo 0 T) :
      d t + ν * (z t) ^ 2 ≤ A t * y t := by
    obtain ⟨d', hd', hb⟩ := hineq ν hν a N g t ht.1.le
    have heq : d t = d' := (hderiv t ht).unique
      (hd'.hasDerivAt (Ici_mem_nhds ht.1))
    dsimp only [z]
    rw [Real.sq_sqrt (highOrderEnergy_nonneg _ _ _), heq]
    exact hb
  have hbudget : (∫ s in (0 : ℝ)..T, A s) ≤ M := by
    have h2 := hH2 N hN g
    have hiE2 : IntervalIntegrable (fun t => highOrderEnergy 2 N (g.coeff t)) volume 0 T :=
      hE2.intervalIntegrable_of_Icc hT.le
    have h2' : (∫ t in (0 : ℝ)..T, highOrderEnergy 2 N (g.coeff t)) ≤ S := by
      simpa only [highOrderEnergy_eq_sobolev_norm_sq, GalerkinSolution.sobolevState] using h2
    dsimp only [A, M]
    rw [intervalIntegral.integral_add (intervalIntegrable_const)
      (hiE2.const_mul (C / ν)), intervalIntegral.integral_const,
      intervalIntegral.integral_const_mul]
    simp only [sub_zero, smul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left h2' (div_nonneg hC.le hν.le)]
  have hb := LINEAR_ENERGY_OF_COEFFICIENT_BUDGET hν.le hT.le hy hz hA
    (fun t _ => highOrderEnergy_nonneg _ _ _) hA_nonneg
    (g.highOrderEnergy_initial_le ha m) hderiv hlinear hbudget
  intro t ht
  have hzsq (s : ℝ) : (z s) ^ 2 = highOrderEnergy (m + 1) N (g.coeff s) :=
    Real.sq_sqrt (highOrderEnergy_nonneg _ _ _)
  simpa only [y, E₀, hzsq, highOrderEnergy_eq_sobolev_norm_sq,
    GalerkinSolution.sobolevState] using hb t ht

theorem local_galerkin_high_order_pointwise
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S)
    (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T, ‖g.sobolevState m t‖ ^ 2 ≤ B := by
  obtain ⟨B, hB, hb⟩ := local_galerkin_high_order_accumulation ν hν a ha T hT S hS hH2 m
  refine ⟨B, hB, ?_⟩
  intro N hN g t ht
  have hi : 0 ≤ ∫ r in (0 : ℝ)..t, ‖g.sobolevState (m + 1) r‖ ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall ht.1 (fun r => sq_nonneg _)
  have h := hb N hN g t ht
  nlinarith [mul_nonneg hν.le hi]

/-- Uniform actual RHS norm in every integral Sobolev order. -/

theorem local_galerkin_high_order_rhs
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S)
    (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ t ∈ Icc (0 : ℝ) T, ‖g.rhsSobolev m t‖ ^ 2 ≤ B := by
  obtain ⟨B2, hB2, hb2⟩ := local_galerkin_high_order_pointwise ν hν a ha T hT S hS hH2 2
  obtain ⟨B1, hB1, hb1⟩ := local_galerkin_high_order_pointwise ν hν a ha T hT S hS hH2 (m + 1)
  obtain ⟨B0, hB0, hb0⟩ := local_galerkin_high_order_pointwise ν hν a ha T hT S hS hH2 (m + 2)
  obtain ⟨C, hC, hrhs⟩ := GALERKIN_SOBOLEV_TIME_DERIVATIVE_BOUND m
  refine ⟨2 * ν ^ 2 * B0 + C * B2 * B1, by positivity, ?_⟩
  intro N hN g t ht
  have h := hrhs ν a N g t ht.1
  rw [g.sobolevState_derivWithin m t ht.1] at h
  have h' : ‖g.rhsSobolev m t‖ ^ 2 ≤
      2 * ν ^ 2 * ‖g.sobolevState (m + 2) t‖ ^ 2 +
        C * ‖g.sobolevState 2 t‖ ^ 2 * ‖g.sobolevState (m + 1) t‖ ^ 2 := by
    simpa only [highOrderEnergy_eq_sobolev_norm_sq, GalerkinSolution.sobolevState] using h
  have hv := mul_le_mul_of_nonneg_left (hb0 N hN g t ht)
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg ν))
  have hp := mul_le_mul_of_nonneg_left
    (mul_le_mul (hb2 N hN g t ht) (hb1 N hN g t ht) (sq_nonneg _) hB2) hC.le
  nlinarith

theorem local_galerkin_high_order_time_modulus
    (ν : ℝ) (hν : 0 < ν) (a : Field) (ha : SmoothSigmaZero a)
    (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hS : 0 ≤ S)
    (hH2 : ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤ S)
    (m : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ N : ℕ, 1 ≤ N → ∀ g : GalerkinSolution ν a N,
      ∀ s ∈ Icc (0 : ℝ) T, ∀ t ∈ Icc (0 : ℝ) T,
        ‖g.sobolevState m t - g.sobolevState m s‖ ^ 2 ≤ B * |t - s| := by
  obtain ⟨B, hB, hb⟩ := local_galerkin_high_order_rhs ν hν a ha T hT S hS hH2 m
  refine ⟨T * B, mul_nonneg hT.le hB, ?_⟩
  intro N hN g s hs t ht
  have henergy : (∫ r in (0 : ℝ)..T, ‖g.rhsSobolev m r‖ ^ 2) ≤ T * B := by
    calc
      _ ≤ ∫ r in (0 : ℝ)..T, B := by
        apply intervalIntegral.integral_mono_on hT.le
          ((((g.rhsSobolev_continuousOn m).mono
            (fun r hr => hr.1)).norm.pow 2).intervalIntegrable_of_Icc hT.le)
          intervalIntegrable_const
        exact hb N hN g
      _ = _ := by simp
  have hordered {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvT : v ≤ T) :
      ‖g.sobolevState m v - g.sobolevState m u‖ ^ 2 ≤ (v - u) * (T * B) :=
    (g.sobolevState_time_modulus m hu huv hvT).trans
      (mul_le_mul_of_nonneg_left henergy (sub_nonneg.mpr huv))
  rcases le_total s t with hst | hts
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hst), mul_comm] using
      hordered hs.1 hst ht.2
  · calc
      _ = ‖g.sobolevState m s - g.sobolevState m t‖ ^ 2 := by rw [norm_sub_rev]
      _ ≤ (s - t) * (T * B) := hordered ht.1 hts hs.2
      _ = (T * B) * |t - s| := by
        rw [abs_of_nonpos (sub_nonpos.mpr hts), neg_sub, mul_comm]

end
end MethbokeAddon.WeakFouriermanB
