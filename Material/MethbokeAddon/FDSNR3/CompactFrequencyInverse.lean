import MethbokeAddon.FDSNR3.ParametricFourier
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Partial Fourier inversion on genuine joint Schwartz functions

The parameter variables are retained while the last Euclidean variable is
Fourier transformed. Recursive Schwartz-valued symbols represent every full
joint Taylor jet. Their uniform integrable decay justifies differentiation,
and the actual Fourier integration-by-parts bounds prove full joint Schwartz
decay. Compact smooth spectra enter through `HasCompactSupport.toSchwartzMap`.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

section Slices

variable (P X : Type*)
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

def rightSliceCLM : X →L[ℝ] (P × X) :=
  (0 : X →L[ℝ] P).prod (ContinuousLinearMap.id ℝ X)

@[simp] theorem rightSliceCLM_apply (x : X) : rightSliceCLM P X x = (0, x) := rfl

def rightSliceAffine (p : P) : X →ᴬ[ℝ] (P × X) where
  toFun x := (p, x)
  linear := (rightSliceCLM P X).toLinearMap
  map_vadd' := by
    intro x v
    change (p, v + x) = ((0 : P), v) + (p, x)
    simp
  cont := continuous_const.prodMk continuous_id

@[simp] theorem rightSliceAffine_apply (p : P) (x : X) :
    rightSliceAffine P X p x = (p, x) := rfl

@[simp] theorem rightSliceAffine_contLinear (p : P) :
    (rightSliceAffine P X p).contLinear = rightSliceCLM P X := by
  ext x <;> rfl

variable {P X}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def schwartzRightSlice (A : 𝓢(P × X, E)) (p : P) : 𝓢(X, E) :=
  SchwartzMap.compCLM ℝ
    (show Function.HasTemperateGrowth (fun x : X => (p, x)) by
      have h := (Function.HasTemperateGrowth.const (E := X) (p, (0 : X))).add
        (rightSliceCLM P X).hasTemperateGrowth
      have heq : ((fun _ : X => (p, (0 : X))) +
          (rightSliceCLM P X : X → P × X)) = (fun x : X => (p, x)) := by
        funext x
        change (p + 0, (0 : X) + x) = (p, x)
        simp only [add_zero, zero_add]
      rw [heq] at h
      exact h)
    ⟨1, 1, fun x => by
      simp only [pow_one, one_mul]
      exact (le_max_right ‖p‖ ‖x‖).trans (by
        change max ‖p‖ ‖x‖ ≤ 1 + max ‖p‖ ‖x‖
        linarith)⟩ A

@[simp] theorem schwartzRightSlice_apply (A : 𝓢(P × X, E)) (p : P) (x : X) :
    schwartzRightSlice A p x = A (p, x) := rfl

theorem schwartzRightSlice_coe (A : 𝓢(P × X, E)) (p : P) :
    (schwartzRightSlice A p : X → E) = fun x : X => A (p, x) := rfl

theorem iteratedFDeriv_schwartzRightSlice (A : 𝓢(P × X, E))
    (p : P) (n : ℕ) (x : X) :
    iteratedFDeriv ℝ n (schwartzRightSlice A p) x =
      (iteratedFDeriv ℝ n A (p, x)).compContinuousLinearMap
        (fun _ : Fin n => rightSliceCLM P X) := by
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have h := ((A.smooth'.of_le hn).contDiffOn.ftaylorSeriesWithin uniqueDiffOn_univ).comp_continuousAffineMap
    (rightSliceAffine P X p)
  have heq := h.eq_iteratedFDerivWithin_of_uniqueDiffOn le_rfl
    (by simpa using (uniqueDiffOn_univ : UniqueDiffOn ℝ (univ : Set X)))
    (by simp : x ∈ rightSliceAffine P X p ⁻¹' (univ : Set (P × X)))
  rw [schwartzRightSlice_coe]
  simpa only [ftaylorSeriesWithin, rightSliceAffine_apply,
    rightSliceAffine_contLinear, preimage_univ, iteratedFDerivWithin_univ,
    Function.comp_def] using! heq.symm

theorem norm_iteratedFDeriv_schwartzRightSlice_le (A : 𝓢(P × X, E))
    (p : P) (n : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) x‖ ≤
      ‖iteratedFDeriv ℝ n A (p, x)‖ * ‖rightSliceCLM P X‖ ^ n := by
  rw [iteratedFDeriv_schwartzRightSlice]
  simpa using (iteratedFDeriv ℝ n A (p, x)).norm_compContinuousLinearMap_le
    (fun _ : Fin n => rightSliceCLM P X)

/-- Independent parameter and integration-variable weights are uniformly
controlled by the genuine joint Schwartz seminorms. -/
theorem schwartzRightSlice_uniform_weighted_jets (A : 𝓢(P × X, E))
    (a b n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, ∀ x : X,
      (1 + ‖p‖) ^ a * (1 + ‖x‖) ^ b *
        ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) x‖ ≤ C := by
  let D : ℝ := 2 ^ (a + b) *
    (Finset.Iic (a + b, n)).sup (fun m => SchwartzMap.seminorm ℝ m.1 m.2) A
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨D * ‖rightSliceCLM P X‖ ^ n, mul_nonneg hD (by positivity), ?_⟩
  intro p x
  have hw : (1 + ‖p‖) ^ a * (1 + ‖x‖) ^ b ≤
      (1 + ‖(p, x)‖) ^ (a + b) := by
    rw [pow_add]
    gcongr
    · exact le_max_left _ _
    · exact le_max_right _ _
  have hfull : (1 + ‖(p, x)‖) ^ (a + b) * ‖iteratedFDeriv ℝ n A (p, x)‖ ≤ D :=
    SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ)
      (m := (a + b, n)) le_rfl le_rfl A (p, x)
  calc
    _ ≤ (1 + ‖(p, x)‖) ^ (a + b) *
        (‖iteratedFDeriv ℝ n A (p, x)‖ * ‖rightSliceCLM P X‖ ^ n) :=
      mul_le_mul hw (norm_iteratedFDeriv_schwartzRightSlice_le A p n x)
        (norm_nonneg _) (by positivity)
    _ = ((1 + ‖(p, x)‖) ^ (a + b) * ‖iteratedFDeriv ℝ n A (p, x)‖) *
        ‖rightSliceCLM P X‖ ^ n := by ring
    _ ≤ D * ‖rightSliceCLM P X‖ ^ n :=
      mul_le_mul_of_nonneg_right hfull (by positivity)

theorem schwartzRightSlice_uniform_decay (A : 𝓢(P × X, E)) (a k n m : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, ∀ x : X,
      ‖p‖ ^ a * ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) x‖ ≤
        C * (1 + ‖x‖) ^ (-(m : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := schwartzRightSlice_uniform_weighted_jets A a (k + m) n
  refine ⟨C, hC, ?_⟩
  intro p x
  have h : (1 + ‖x‖) ^ m *
      (‖p‖ ^ a * ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) x‖) ≤ C := by
    calc
      _ ≤ (1 + ‖x‖) ^ m * ((1 + ‖p‖) ^ a * (1 + ‖x‖) ^ k *
          ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) x‖) := by
        gcongr <;> linarith
      _ = (1 + ‖p‖) ^ a * (1 + ‖x‖) ^ (k + m) *
          ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) x‖ := by rw [pow_add]; ring
      _ ≤ C := hbound p x
  have hp : 0 < (1 + ‖x‖) ^ m := by positivity
  calc
    _ ≤ C / (1 + ‖x‖) ^ m := (le_div_iff₀ hp).mpr (by simpa only [mul_comm] using h)
    _ = C * (1 + ‖x‖) ^ (-(m : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      rfl

end Slices

section Fourier

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem schwartzFrequencySlice_uniform_integrals (A : 𝓢(P × Vec, E)) (a k n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P,
      ‖p‖ ^ a * (∫ ξ : Vec, ‖ξ‖ ^ k *
        ‖iteratedFDeriv ℝ n (schwartzRightSlice A p) ξ‖) ≤ C := by
  let m := (volume : Measure Vec).integrablePower
  obtain ⟨D, hD, hbound⟩ := schwartzRightSlice_uniform_decay A a k n m
  let B : Vec → ℝ := fun ξ => D * (1 + ‖ξ‖) ^ (-(m : ℝ))
  have hB : Integrable B :=
    ((volume : Measure Vec).integrable_pow_neg_integrablePower).const_mul D
  refine ⟨∫ ξ, B ξ, integral_nonneg (fun ξ => mul_nonneg hD (Real.rpow_nonneg (by positivity) _)), ?_⟩
  intro p
  rw [← integral_const_mul]
  apply integral_mono
    ((SchwartzMap.integrable_pow_mul_iteratedFDeriv volume (schwartzRightSlice A p) k n).const_mul
      (‖p‖ ^ a)) hB
  intro ξ
  simpa only [B, mul_assoc] using hbound p ξ

theorem schwartzFrequencySlice_dominated (A : 𝓢(P × Vec, E)) :
    ∃ B : Vec → ℝ, Integrable B ∧ ∀ p : P, ∀ ξ : Vec, ‖A (p, ξ)‖ ≤ B ξ := by
  let m := (volume : Measure Vec).integrablePower
  obtain ⟨C, _, hbound⟩ := schwartzRightSlice_uniform_decay A 0 0 0 m
  refine ⟨fun ξ => C * (1 + ‖ξ‖) ^ (-(m : ℝ)),
    ((volume : Measure Vec).integrable_pow_neg_integrablePower).const_mul C, ?_⟩
  simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero, schwartzRightSlice_apply] using hbound

def parameterProjectionCLM (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (P × Vec) →L[ℝ] (P × Vec) :=
  (ContinuousLinearMap.fst ℝ P Vec).prod (0 : (P × Vec) →L[ℝ] Vec)

@[simp] theorem parameterProjectionCLM_apply (q : P × Vec) :
    parameterProjectionCLM P q = (q.1, 0) := rfl

def frequencyPairingCLM (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (P × Vec) →L[ℝ] (P × Vec) →L[ℝ] ℝ :=
  ((ContinuousLinearMap.compL ℝ (P × Vec) Vec ℝ).flip
    (ContinuousLinearMap.snd ℝ P Vec)).comp
      ((innerSL ℝ).comp (ContinuousLinearMap.snd ℝ P Vec))

@[simp] theorem frequencyPairingCLM_apply (z q : P × Vec) :
    frequencyPairingCLM P z q = inner ℝ z.2 q.2 := rfl

def partialFourierJetStep (A : 𝓢(P × Vec, E)) :
    𝓢(P × Vec, (P × Vec) →L[ℝ] E) :=
  SchwartzMap.postcompCLM
      ((ContinuousLinearMap.compL ℝ (P × Vec) (P × Vec) E).flip (parameterProjectionCLM P))
      (SchwartzMap.fderivCLM ℝ (P × Vec) E A) +
    (-(2 * (Real.pi : ℂ) * Complex.I)) •
      SchwartzMap.smulRightCLM ℝ E (frequencyPairingCLM P) A

@[simp] theorem partialFourierJetStep_apply (A : 𝓢(P × Vec, E)) (z q : P × Vec) :
    partialFourierJetStep A z q =
      fderiv ℝ A z (q.1, 0) +
        (-(2 * (Real.pi : ℂ) * Complex.I)) • ((inner ℝ z.2 q.2) • A z) := rfl

def partialFourierJet (A : 𝓢(P × Vec, E)) :
    (n : ℕ) → 𝓢(P × Vec, (P × Vec) [×n]→L[ℝ] E)
  | 0 => SchwartzMap.postcompCLM
      (continuousMultilinearCurryFin0 ℝ (P × Vec) E).symm.toContinuousLinearEquiv.toContinuousLinearMap A
  | n + 1 => SchwartzMap.postcompCLM
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P × Vec) E).symm.toContinuousLinearEquiv.toContinuousLinearMap
      (partialFourierJetStep (partialFourierJet A n))

@[simp] theorem partialFourierJet_zero_apply (A : 𝓢(P × Vec, E)) (z : P × Vec)
    (m : Fin 0 → P × Vec) : partialFourierJet A 0 z m = A z := rfl

@[simp] theorem partialFourierJet_succ_apply (A : 𝓢(P × Vec, E)) (n : ℕ)
    (z : P × Vec) (m : Fin (n + 1) → P × Vec) :
    partialFourierJet A (n + 1) z m =
      partialFourierJetStep (partialFourierJet A n) z (m 0) (Fin.tail m) := rfl

def partialFourierTaylor (A : 𝓢(P × Vec, E)) (ξ : Vec) (q : P × Vec) :
    FormalMultilinearSeries ℝ (P × Vec) E :=
  fun n => Real.fourierChar (-inner ℝ ξ q.2) • partialFourierJet A n (q.1, ξ)

theorem partialFourierTaylor_hasFDerivAt (A : 𝓢(P × Vec, E))
    (ξ : Vec) (n : ℕ) (q : P × Vec) :
    HasFDerivAt (fun y => partialFourierTaylor A ξ y n)
      (partialFourierTaylor A ξ q (n + 1)).curryLeft q := by
  let B := partialFourierJet A n
  have hp : HasFDerivAt (fun y : P × Vec => (y.1, ξ)) (parameterProjectionCLM P) q :=
    (ContinuousLinearMap.fst ℝ P Vec).hasFDerivAt.prodMk (hasFDerivAt_const ξ q)
  have hB := B.differentiableAt.hasFDerivAt.comp q hp
  have hc := (Real.hasFDerivAt_fourierChar_neg_bilinear_right (innerSL ℝ) ξ q.2).comp q
    (ContinuousLinearMap.snd ℝ P Vec).hasFDerivAt
  have hprod := hc.smul hB
  have hder := hprod.congr_fderiv (g' :=
      (partialFourierTaylor A ξ q (n + 1)).curryLeft)
  suffices h : HasFDerivAt
      (fun y : P × Vec => (Real.fourierChar (-inner ℝ ξ y.2) : ℂ) • B (y.1, ξ))
      (partialFourierTaylor A ξ q (n + 1)).curryLeft q by
    simpa only [partialFourierTaylor, B, Circle.smul_def] using! h
  apply hder
  · apply ContinuousLinearMap.ext
    intro v
    apply ContinuousMultilinearMap.ext
    intro m
    change
      (Real.fourierChar (-inner ℝ ξ q.2) : ℂ) • fderiv ℝ B (q.1, ξ) (v.1, 0) m +
        ((-2 * (Real.pi : ℂ) * Complex.I * Real.fourierChar (-inner ℝ ξ q.2)) *
          (inner ℝ ξ v.2 : ℂ)) • B (q.1, ξ) m =
      ((Real.fourierChar (-inner ℝ ξ q.2) : ℂ) •
        (fderiv ℝ B (q.1, ξ) (v.1, 0) m +
          (-(2 * (Real.pi : ℂ) * Complex.I)) • ((inner ℝ ξ v.2) • B (q.1, ξ) m)))
    rw [smul_add]
    congr 1
    simp only [← Complex.coe_smul, smul_smul]
    congr 1
    ring

theorem partialFourierTaylor_isTaylor (A : 𝓢(P × Vec, E)) (ξ : Vec) :
    HasFTaylorSeriesUpToOn ∞
      (fun q : P × Vec => Real.fourierChar (-inner ℝ ξ q.2) • A (q.1, ξ))
      (partialFourierTaylor A ξ) univ := by
  constructor
  · intro q _
    change (Real.fourierChar (-inner ℝ ξ q.2) : ℂ) • A (q.1, ξ) =
      (Real.fourierChar (-inner ℝ ξ q.2) : ℂ) • A (q.1, ξ)
    rfl
  · intro n _ q _
    exact (partialFourierTaylor_hasFDerivAt A ξ n q).hasFDerivWithinAt
  · intro n _
    exact fun q _ => (partialFourierTaylor_hasFDerivAt A ξ n q).continuousAt.continuousWithinAt

def partialFourierTransform (A : 𝓢(P × Vec, E)) (q : P × Vec) : E :=
  𝓕 (fun ξ : Vec => A (q.1, ξ)) q.2

theorem partialFourierTransform_hasTaylor (A : 𝓢(P × Vec, E)) :
    HasFTaylorSeriesUpToOn ∞ (partialFourierTransform A)
      (fun q n => ∫ ξ : Vec, partialFourierTaylor A ξ q n) univ := by
  have hMeas : ∀ n : ℕ, ∀ q ∈ (univ : Set (P × Vec)),
      AEStronglyMeasurable (fun ξ : Vec => partialFourierTaylor A ξ q n) := by
    intro n q _
    have hB : Continuous (fun ξ : Vec => partialFourierJet A n (q.1, ξ)) :=
      (partialFourierJet A n).continuous.comp (continuous_const.prodMk continuous_id)
    exact ((Real.continuous_fourierChar.comp (by fun_prop)).smul hB).aestronglyMeasurable
  have hbound : ∀ n : ℕ, ∃ B : Vec → ℝ, Integrable B ∧
      ∀ ξ : Vec, ∀ q ∈ (univ : Set (P × Vec)), ‖partialFourierTaylor A ξ q n‖ ≤ B ξ := by
    intro n
    obtain ⟨B, hB, hbound⟩ := schwartzFrequencySlice_dominated (partialFourierJet A n)
    refine ⟨B, hB, ?_⟩
    intro ξ q _
    change ‖(Real.fourierChar (-inner ℝ ξ q.2) : ℂ) •
      partialFourierJet A n (q.1, ξ)‖ ≤ B ξ
    rw [norm_smul, Circle.norm_coe, one_mul]
    exact hbound q.1 ξ
  have hF : partialFourierTransform A =
      (fun q : P × Vec => ∫ ξ : Vec,
        Real.fourierChar (-inner ℝ ξ q.2) • A (q.1, ξ)) := by
    funext q
    exact Real.fourier_eq (fun ξ : Vec => A (q.1, ξ)) q.2
  rw [hF]
  exact integral_hasFTaylorSeriesUpToOn_of_dominated isOpen_univ
    (partialFourierTaylor_isTaylor A) hMeas hbound

theorem partialFourierTransform_smooth (A : 𝓢(P × Vec, E)) :
    ContDiff ℝ ∞ (partialFourierTransform A) :=
  contDiffOn_univ.mp (partialFourierTransform_hasTaylor A).contDiffOn

theorem partialFourierTransform_iteratedFDeriv (A : 𝓢(P × Vec, E))
    (n : ℕ) (q : P × Vec) :
    iteratedFDeriv ℝ n (partialFourierTransform A) q =
      𝓕 (fun ξ : Vec => partialFourierJet A n (q.1, ξ)) q.2 := by
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have h := (partialFourierTransform_hasTaylor A).eq_iteratedFDerivWithin_of_uniqueDiffOn
    hn uniqueDiffOn_univ (mem_univ q)
  simpa only [iteratedFDerivWithin_univ, partialFourierTaylor, Real.fourier_eq] using h.symm

theorem partialFourierTransform_parameter_weight (A : 𝓢(P × Vec, E)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, ∀ x : Vec,
      ‖p‖ ^ N * ‖𝓕 (fun ξ : Vec => A (p, ξ)) x‖ ≤ C := by
  obtain ⟨C, hC, hbound⟩ := schwartzFrequencySlice_uniform_integrals A N 0 0
  refine ⟨C, hC, ?_⟩
  intro p x
  have hnorm : ‖𝓕 (fun ξ : Vec => A (p, ξ)) x‖ ≤ ∫ ξ : Vec, ‖A (p, ξ)‖ := by
    rw [Real.fourier_eq]
    simpa only [Circle.norm_smul] using
      norm_integral_le_integral_norm (fun ξ : Vec => Real.fourierChar (-inner ℝ ξ x) • A (p, ξ))
  exact (mul_le_mul_of_nonneg_left hnorm (by positivity)).trans
    (by simpa only [pow_zero, one_mul, norm_iteratedFDeriv_zero,
      schwartzRightSlice_apply] using hbound p)

theorem partialFourierTransform_spatial_weight (A : 𝓢(P × Vec, E)) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p : P, ∀ x : Vec,
      ‖x‖ ^ N * ‖𝓕 (fun ξ : Vec => A (p, ξ)) x‖ ≤ C := by
  choose D hD hbound using (fun k n : ℕ => schwartzFrequencySlice_uniform_integrals A 0 k n)
  let S : Finset (ℕ × ℕ) := Finset.range (0 + 1) ×ˢ Finset.range (N + 1)
  have hsum : 0 ≤ ∑ j ∈ S, D j.1 j.2 := Finset.sum_nonneg (fun j _ => hD j.1 j.2)
  refine ⟨(2 * Real.pi) ^ (0 : ℕ) * (2 * (0 : ℝ) + 2) ^ N *
      ∑ j ∈ S, D j.1 j.2, mul_nonneg (by positivity) hsum, ?_⟩
  intro p x
  rw [← schwartzRightSlice_coe A p]
  have h := Real.pow_mul_norm_iteratedFDeriv_fourier_le
    ((schwartzRightSlice A p).smooth ⊤)
    (fun k n _ _ => SchwartzMap.integrable_pow_mul_iteratedFDeriv volume
      (schwartzRightSlice A p) k n)
    (k := 0) (n := N) le_top le_top x
  simp only [norm_iteratedFDeriv_zero] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  change (∑ j ∈ S, ∫ ξ : Vec, ‖ξ‖ ^ j.1 *
      ‖iteratedFDeriv ℝ j.2 (schwartzRightSlice A p) ξ‖) ≤ ∑ j ∈ S, D j.1 j.2
  apply Finset.sum_le_sum
  intro j hj
  simpa only [pow_zero, one_mul] using hbound j.1 j.2 p

theorem partialFourierTransform_decay (A : 𝓢(P × Vec, E)) (N n : ℕ) :
    ∃ C : ℝ, ∀ q : P × Vec,
      ‖q‖ ^ N * ‖iteratedFDeriv ℝ n (partialFourierTransform A) q‖ ≤ C := by
  obtain ⟨Cp, hCp, hp⟩ := partialFourierTransform_parameter_weight (partialFourierJet A n) N
  obtain ⟨Cx, hCx, hx⟩ := partialFourierTransform_spatial_weight (partialFourierJet A n) N
  refine ⟨Cp + Cx, ?_⟩
  rintro ⟨p, x⟩
  rw [partialFourierTransform_iteratedFDeriv, Prod.norm_def]
  rcases le_total ‖p‖ ‖x‖ with h | h
  · rw [max_eq_right h]
    exact (hx p x).trans (le_add_of_nonneg_left hCp)
  · rw [max_eq_left h]
    exact (hp p x).trans (le_add_of_nonneg_right hCx)

/-- Partial Fourier transform is a genuine Schwartz map in all variables. -/
def partialFourierSchwartz (A : 𝓢(P × Vec, E)) : 𝓢(P × Vec, E) where
  toFun := partialFourierTransform A
  smooth' := partialFourierTransform_smooth A
  decay' := partialFourierTransform_decay A

@[simp] theorem partialFourierSchwartz_apply (A : 𝓢(P × Vec, E)) (p : P) (x : Vec) :
    partialFourierSchwartz A (p, x) = 𝓕 (fun ξ : Vec => A (p, ξ)) x := rfl

def frequencyReflection (P : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P] :
    (P × Vec) ≃ₗᵢ[ℝ] (P × Vec) where
  toLinearEquiv := (LinearIsometryEquiv.refl ℝ P).toLinearEquiv.prodCongr
    (LinearIsometryEquiv.neg ℝ (E := Vec)).toLinearEquiv
  norm_map' := by
    intro q
    change max ‖q.1‖ ‖-q.2‖ = max ‖q.1‖ ‖q.2‖
    rw [norm_neg]

@[simp] theorem frequencyReflection_apply (p : P) (x : Vec) :
    frequencyReflection P (p, x) = (p, -x) := rfl

def partialFourierInverse (A : 𝓢(P × Vec, E)) : 𝓢(P × Vec, E) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ (frequencyReflection P).toContinuousLinearEquiv
    (partialFourierSchwartz A)

@[simp] theorem partialFourierInverse_apply (A : 𝓢(P × Vec, E)) (p : P) (x : Vec) :
    partialFourierInverse A (p, x) = 𝓕⁻ (fun ξ : Vec => A (p, ξ)) x := by
  change 𝓕 (fun ξ : Vec => A (p, ξ)) (-x) = 𝓕⁻ (fun ξ : Vec => A (p, ξ)) x
  exact (Real.fourierInv_eq_fourier_neg (fun ξ : Vec => A (p, ξ)) x).symm

theorem partialFourierInverse_zero_fiber (A : 𝓢(P × Vec, E)) {p : P}
    (hp : ∀ ξ : Vec, A (p, ξ) = 0) (x : Vec) : partialFourierInverse A (p, x) = 0 := by
  rw [partialFourierInverse_apply]
  have h : (fun ξ : Vec => A (p, ξ)) = 0 := funext hp
  simp only [h, Real.fourierInv_eq, Pi.zero_apply, smul_zero, integral_zero]

end Fourier

end

end MethbokeAddon.FDSNR3
