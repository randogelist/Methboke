import MethbokeAddon.FDSNR3.ParametricFourier

/-!
# Joint smoothness of the actual forward Fourier transform

The oscillatory kernel is treated as a function with temperate growth.
All source jets retain the weighted bounds from the original LocalSchwartz
contract. No additional Fourier regularity premise is introduced.

Prepared by static inspection; external compilation and exact audits govern
acceptance.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

set_option backward.isDefEq.respectTransparency false in
/-- All Taylor jets of the scalar Fourier character are obtained from the
library Fourier Taylor formula with a Dirac measure. -/
theorem fourierChar_neg_hasTemperateGrowth :
    Function.HasTemperateGrowth (fun r : ℝ => (Real.fourierChar (-r) : ℂ)) := by
  let L : ℝ →L[ℝ] ℝ →L[ℝ] ℝ := ContinuousLinearMap.mul ℝ ℝ
  have hInt : ∀ n : ℕ, (n : ℕ∞ω) ≤ ∞ →
      Integrable (fun v : ℝ => ‖v‖ ^ n * ‖(1 : ℂ)‖) (Measure.dirac 1) :=
    fun _ _ => integrable_dirac (by simp)
  have hFourier :
      VectorFourier.fourierIntegral Real.fourierChar (Measure.dirac (1 : ℝ))
          L.toLinearMap₁₂ (fun _ : ℝ => (1 : ℂ)) =
        (fun r : ℝ => (Real.fourierChar (-r) : ℂ)) := by
    funext r
    simp [VectorFourier.fourierIntegral, L, Circle.smul_def]
  have hTaylor : HasFTaylorSeriesUpTo ∞
      (fun r : ℝ => (Real.fourierChar (-r) : ℂ))
      (fun r n => (Real.fourierChar (-r) : ℂ) •
        VectorFourier.fourierPowSMulRight L (fun _ : ℝ => (1 : ℂ)) 1 n) := by
    have h := VectorFourier.hasFTaylorSeriesUpTo_fourierIntegral L
      (μ := Measure.dirac (1 : ℝ)) (f := fun _ : ℝ => (1 : ℂ))
      hInt aestronglyMeasurable_const
    rw [hFourier] at h
    simpa [VectorFourier.fourierIntegral, L, Circle.smul_def] using h
  refine ⟨hTaylor.contDiff, ?_⟩
  intro n
  refine ⟨0, (2 * Real.pi * ‖L‖) ^ n, ?_⟩
  intro r
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  let A : ContinuousMultilinearMap ℝ (fun _ : Fin n => ℝ) ℂ :=
    VectorFourier.fourierPowSMulRight L (fun _ : ℝ => (1 : ℂ)) 1 n
  have hjet : iteratedFDeriv ℝ n
      (fun r : ℝ => (Real.fourierChar (-r) : ℂ)) r =
        (Real.fourierChar (-r) : ℂ) • A :=
    (hTaylor.eq_iteratedFDeriv hn r).symm
  calc
    ‖iteratedFDeriv ℝ n (fun r : ℝ => (Real.fourierChar (-r) : ℂ)) r‖ =
        ‖(Real.fourierChar (-r) : ℂ) • A‖ := congrArg norm hjet
    _ ≤ ‖(Real.fourierChar (-r) : ℂ)‖ * ‖A‖ :=
      ContinuousMultilinearMap.opNorm_smul_le _ A
    _ = ‖A‖ := by rw [Circle.norm_coe, one_mul]
    _ ≤ (2 * Real.pi * ‖L‖) ^ n := by
      simpa only [A, norm_one, one_pow, mul_one] using
        VectorFourier.norm_fourierPowSMulRight_le L (fun _ : ℝ => (1 : ℂ)) 1 n
    _ = (2 * Real.pi * ‖L‖) ^ n * (1 + ‖r‖) ^ 0 := by
      rw [pow_zero, mul_one]

/-- Physical time and integration position, forgetting the Fourier
parameter but retaining its full tangent-space representation. -/
def fourierSourceCLM : ((ℝ × Vec) × Vec) →L[ℝ] (ℝ × Vec) :=
  ((ContinuousLinearMap.fst ℝ ℝ Vec).comp
    (ContinuousLinearMap.fst ℝ (ℝ × Vec) Vec)).prod
      (ContinuousLinearMap.snd ℝ (ℝ × Vec) Vec)

@[simp] theorem fourierSourceCLM_apply (q : ℝ × Vec) (x : Vec) :
    fourierSourceCLM (q, x) = (q.1, x) := rfl

/-- The literal kernel of Mathlib's real Fourier transform. -/
def jointFourierKernel (z : (ℝ × Vec) × Vec) : ℂ :=
  Real.fourierChar (-inner ℝ z.2 z.1.2)

theorem jointFourierKernel_hasTemperateGrowth :
    Function.HasTemperateGrowth jointFourierKernel := by
  have hi : Function.HasTemperateGrowth
      (fun z : (ℝ × Vec) × Vec => inner ℝ z.2 z.1.2) :=
    (innerSL ℝ).bilinear_hasTemperateGrowth
      (ContinuousLinearMap.snd ℝ (ℝ × Vec) Vec).hasTemperateGrowth
      ((ContinuousLinearMap.snd ℝ ℝ Vec).comp
        (ContinuousLinearMap.fst ℝ (ℝ × Vec) Vec)).hasTemperateGrowth
  exact fourierChar_neg_hasTemperateGrowth.comp hi

def fourierParameterBox (b R : ℝ) : Set (ℝ × Vec) :=
  Ioo (0 : ℝ) b ×ˢ Metric.ball (0 : Vec) R

theorem isOpen_fourierParameterBox (b R : ℝ) : IsOpen (fourierParameterBox b R) :=
  isOpen_Ioo.prod Metric.isOpen_ball

theorem norm_le_of_mem_fourierParameterBox {b R : ℝ} (hR : 0 < R)
    {q : ℝ × Vec} (hq : q ∈ fourierParameterBox b R) : ‖q‖ ≤ b + R := by
  have hb : 0 < b := hq.1.1.trans hq.1.2
  have hξ : ‖q.2‖ < R := by simpa only [Metric.mem_ball, dist_zero_right] using hq.2
  rw [Prod.norm_def, Real.norm_eq_abs, abs_of_pos hq.1.1]
  exact max_le (by linarith [hq.1.2]) (by linarith)

/-- The genuine joint Fourier integrand, with the complex Euclidean
velocity and the actual continuous-frequency character. -/
def jointFourierIntegrand (u : Velocity) (z : (ℝ × Vec) × Vec) : CVec :=
  jointFourierKernel z • complexify (u z.1.1 z.2)

theorem LocalSchwartz.contDiffOn_jointFourierIntegrand {T b R : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) :
    ContDiffOn ℝ ∞ (jointFourierIntegrand u) (fourierParameterBox b R ×ˢ univ) := by
  have hu' : ContDiffOn ℝ ∞
      ((fun z : ℝ × Vec => u z.1 z.2) ∘ fourierSourceCLM)
      (fourierParameterBox b R ×ˢ univ) :=
    hu.1.comp fourierSourceCLM.contDiff.contDiffOn (fun z hz =>
      show z.1.1 ∈ Ico (0 : ℝ) T from ⟨hz.1.1.1.le, hz.1.1.2.trans hb.2⟩)
  exact jointFourierKernel_hasTemperateGrowth.1.contDiffOn.smul
    (complexifyCLM.contDiff.comp_contDiffOn hu')

/-- The source jet under the linear inclusion is bounded by the original
physical joint jet. The Fourier frequency does not enter the bound. -/
theorem LocalSchwartz.norm_fourier_source_jet_le {T b R : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T)
    {q : ℝ × Vec} (hq : q ∈ fourierParameterBox b R) (x : Vec) (n : ℕ) :
    ‖iteratedFDerivWithin ℝ n
      (fun z : (ℝ × Vec) × Vec => complexify (u z.1.1 z.2))
      (fourierParameterBox b R ×ˢ univ) (q, x)‖ ≤
      ‖complexifyCLM‖ * ‖fourierSourceCLM‖ ^ n *
        ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
          (preterminalSpacetime T) (q.1, x)‖ := by
  let S := fourierParameterBox b R ×ˢ (univ : Set Vec)
  have hs : IsOpen S := (isOpen_fourierParameterBox b R).prod isOpen_univ
  have hz : (q, x) ∈ S := ⟨hq, mem_univ x⟩
  have htime : (q.1, x) ∈ preterminalSpacetime T :=
    ⟨hq.1.1.le, hq.1.2.trans hb.2⟩
  have hpre : fourierSourceCLM ⁻¹' preterminalSpacetime T =
      preterminalSpacetime T ×ˢ (univ : Set Vec) := by
    ext z
    simp [preterminalSpacetime, fourierSourceCLM]
  have hpreunique : UniqueDiffOn ℝ (fourierSourceCLM ⁻¹' preterminalSpacetime T) := by
    rw [hpre]
    exact (uniqueDiffOn_preterminalSpacetime T).prod uniqueDiffOn_univ
  have hpre_nhds : fourierSourceCLM ⁻¹' preterminalSpacetime T ∈ 𝓝 (q, x) :=
    fourierSourceCLM.continuous.continuousAt.preimage_mem_nhds
      (preterminalSpacetime_mem_nhds ⟨hq.1.1, hq.1.2.trans hb.2⟩ x)
  have hsets : S =ᶠ[𝓝 (q, x)] (fourierSourceCLM ⁻¹' preterminalSpacetime T) :=
    (Filter.eventuallyEq_univ.mpr (hs.mem_nhds hz)).trans
      (Filter.eventuallyEq_univ.mpr hpre_nhds).symm
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hu' : ContDiffOn ℝ ∞
      ((fun z : ℝ × Vec => u z.1 z.2) ∘ fourierSourceCLM) S :=
    hu.1.comp fourierSourceCLM.contDiff.contDiffOn (fun z hz =>
      show z.1.1 ∈ Ico (0 : ℝ) T from ⟨hz.1.1.1.le, hz.1.1.2.trans hb.2⟩)
  have hchain : iteratedFDerivWithin ℝ n
      ((fun z : ℝ × Vec => u z.1 z.2) ∘ fourierSourceCLM) S (q, x) =
      (iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (q.1, x)).compContinuousLinearMap
          (fun _ : Fin n => fourierSourceCLM) := by
    rw [iteratedFDerivWithin_congr_set hsets n]
    exact fourierSourceCLM.iteratedFDerivWithin_comp_right hu.1
      (uniqueDiffOn_preterminalSpacetime T) hpreunique htime hn
  have hsource : ‖iteratedFDerivWithin ℝ n
      ((fun z : ℝ × Vec => u z.1 z.2) ∘ fourierSourceCLM) S (q, x)‖ ≤
      ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (q.1, x)‖ * ‖fourierSourceCLM‖ ^ n := by
    rw [hchain]
    simpa using (iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T) (q.1, x)).norm_compContinuousLinearMap_le
        (fun _ : Fin n => fourierSourceCLM)
  exact (complexifyCLM.norm_iteratedFDerivWithin_comp_left (hu' (q, x) hz)
    hs.uniqueDiffOn hz hn).trans
      ((mul_le_mul_of_nonneg_left hsource (norm_nonneg complexifyCLM)).trans_eq (by ring))

/-- Cancellation of the polynomial growth of the oscillatory kernel
against the stronger inverse-polynomial source bound. -/
theorem pow_mul_rpow_neg_add (a : ℝ) (ha : 0 < a) (k m : ℕ) :
    a ^ k * a ^ (-((k + m : ℕ) : ℝ)) = a ^ (-(m : ℝ)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add ha]
  congr 1
  push_cast
  ring

/-- Every full joint derivative of the actual Fourier integrand has an
integrable common bound on each bounded time-frequency box. -/
theorem LocalSchwartz.jointFourierIntegrand_jet_bound {T b R : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) (hR : 0 < R) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ q ∈ fourierParameterBox b R, ∀ x : Vec,
      ‖iteratedFDerivWithin ℝ n (jointFourierIntegrand u)
        (fourierParameterBox b R ×ˢ univ) (q, x)‖ ≤
          C * (1 + ‖x‖) ^ (-((volume : Measure Vec).integrablePower : ℝ)) := by
  classical
  let S := fourierParameterBox b R ×ˢ (univ : Set Vec)
  let m := (volume : Measure Vec).integrablePower
  have hs : IsOpen S := (isOpen_fourierParameterBox b R).prod isOpen_univ
  obtain ⟨k, C, hC, hkernel⟩ :=
    jointFourierKernel_hasTemperateGrowth.norm_iteratedFDeriv_le_uniform n
  choose D hD_nonneg hD using (fun j : ℕ => hu.uniform_jet_decay hb (k + m) j)
  let K := C * (1 + b + R) ^ k
  let A : ℕ → ℝ := fun j => ‖complexifyCLM‖ * ‖fourierSourceCLM‖ ^ j * D j
  let B : ℂ →L[ℝ] CVec →L[ℝ] CVec := ContinuousLinearMap.lsmul ℝ ℂ
  have hbase : 0 ≤ 1 + b + R := by linarith [hb.1]
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hA : ∀ j : ℕ, 0 ≤ A j := by
    intro j
    exact mul_nonneg (mul_nonneg (norm_nonneg _) (pow_nonneg (norm_nonneg _) _))
      (hD_nonneg j)
  refine ⟨‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K * A (n - i),
    mul_nonneg (ContinuousLinearMap.opNorm_nonneg B) (Finset.sum_nonneg (fun i _ =>
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hK) (hA (n - i)))), ?_⟩
  intro q hq x
  have hz : (q, x) ∈ S := ⟨hq, mem_univ x⟩
  have hn : (n : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
  have hnorm : 1 + ‖(q, x)‖ ≤ (1 + b + R) * (1 + ‖x‖) := by
    have hqnorm := norm_le_of_mem_fourierParameterBox hR hq
    have hbR : 0 ≤ b + R := add_nonneg hb.1 hR.le
    rw [Prod.norm_def]
    calc
      1 + max ‖q‖ ‖x‖ ≤ 1 + (b + R + ‖x‖) :=
        add_le_add (le_refl (1 : ℝ)) (max_le
          (hqnorm.trans (le_add_of_nonneg_right (norm_nonneg x)))
          (le_add_of_nonneg_left hbR))
      _ ≤ (1 + b + R) * (1 + ‖x‖) := by
        nlinarith [mul_nonneg hbR (norm_nonneg x)]
  have hkernel' : ∀ i : ℕ, i ≤ n →
      ‖iteratedFDerivWithin ℝ i jointFourierKernel S (q, x)‖ ≤ K * (1 + ‖x‖) ^ k := by
    intro i hi
    calc
      ‖iteratedFDerivWithin ℝ i jointFourierKernel S (q, x)‖ =
          ‖iteratedFDeriv ℝ i jointFourierKernel (q, x)‖ := by
        rw [iteratedFDerivWithin_of_isOpen i hs hz]
      _ ≤ C * (1 + ‖(q, x)‖) ^ k := hkernel i hi (q, x)
      _ ≤ C * ((1 + b + R) * (1 + ‖x‖)) ^ k := by gcongr <;> assumption
      _ = K * (1 + ‖x‖) ^ k := by dsimp [K]; rw [mul_pow]; ring
  have hsource : ∀ j : ℕ,
      ‖iteratedFDerivWithin ℝ j
        (fun z : (ℝ × Vec) × Vec => complexify (u z.1.1 z.2)) S (q, x)‖ ≤
        A j * (1 + ‖x‖) ^ (-((k + m : ℕ) : ℝ)) := by
    intro j
    exact (hu.norm_fourier_source_jet_le hb hq x j).trans
      ((mul_le_mul_of_nonneg_left (hD j q.1 ⟨hq.1.1.le, hq.1.2.le⟩ x)
        (mul_nonneg (norm_nonneg complexifyCLM) (pow_nonneg (norm_nonneg _) j))).trans_eq
        (by dsimp [A]; ring))
  have hu' : ContDiffOn ℝ ∞
      ((fun z : ℝ × Vec => u z.1 z.2) ∘ fourierSourceCLM) S :=
    hu.1.comp fourierSourceCLM.contDiff.contDiffOn (fun z hz =>
      show z.1.1 ∈ Ico (0 : ℝ) T from ⟨hz.1.1.1.le, hz.1.1.2.trans hb.2⟩)
  have hbilin := B.norm_iteratedFDerivWithin_le_of_bilinear
    jointFourierKernel_hasTemperateGrowth.1.contDiffOn
    (complexifyCLM.contDiff.comp_contDiffOn hu') hs.uniqueDiffOn hz hn
  refine hbilin.trans ?_
  calc
    ‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDerivWithin ℝ i jointFourierKernel S (q, x)‖ *
        ‖iteratedFDerivWithin ℝ (n - i)
          (fun z : (ℝ × Vec) × Vec => complexify (u z.1.1 z.2)) S (q, x)‖
      ≤ ‖B‖ * ∑ i ∈ Finset.range (n + 1),
          ((n.choose i : ℝ) * K * A (n - i)) * (1 + ‖x‖) ^ (-(m : ℝ)) := by
        apply mul_le_mul_of_nonneg_left _ (ContinuousLinearMap.opNorm_nonneg B)
        apply Finset.sum_le_sum
        intro i hi
        have hin : i ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        calc
          (n.choose i : ℝ) * ‖iteratedFDerivWithin ℝ i jointFourierKernel S (q, x)‖ *
              ‖iteratedFDerivWithin ℝ (n - i)
                (fun z : (ℝ × Vec) × Vec => complexify (u z.1.1 z.2)) S (q, x)‖
            ≤ (n.choose i : ℝ) * (K * (1 + ‖x‖) ^ k) *
                (A (n - i) * (1 + ‖x‖) ^ (-((k + m : ℕ) : ℝ))) := by
              gcongr
              · exact hkernel' i hin
              · exact hsource (n - i)
          _ = ((n.choose i : ℝ) * K * A (n - i)) *
              ((1 + ‖x‖) ^ k * (1 + ‖x‖) ^ (-((k + m : ℕ) : ℝ))) := by ring
          _ = ((n.choose i : ℝ) * K * A (n - i)) *
              (1 + ‖x‖) ^ (-(m : ℝ)) := by
            rw [pow_mul_rpow_neg_add _ (by positivity)]
    _ = (‖B‖ * ∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * K * A (n - i)) *
        (1 + ‖x‖) ^ (-(m : ℝ)) := by rw [← Finset.sum_mul]; ring

/-- Actual joint C∞ regularity of the whole-space Fourier transform on a
bounded positive preterminal time-frequency box. -/
theorem LocalSchwartz.contDiffOn_fourierVelocity_box {T b R : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) (hR : 0 < R) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Vec => fourierVelocity (u q.1) q.2)
      (fourierParameterBox b R) := by
  have hdom : ∀ n : ℕ, ∃ B : Vec → ℝ, Integrable B ∧
      ∀ q ∈ fourierParameterBox b R, ∀ x : Vec,
        ‖iteratedFDerivWithin ℝ n (jointFourierIntegrand u)
          (fourierParameterBox b R ×ˢ univ) (q, x)‖ ≤ B x := by
    intro n
    obtain ⟨C, _, hC⟩ := hu.jointFourierIntegrand_jet_bound hb hR n
    exact ⟨fun x => C * (1 + ‖x‖) ^ (-((volume : Measure Vec).integrablePower : ℝ)),
      ((volume : Measure Vec).integrable_pow_neg_integrablePower).const_mul C, hC⟩
  have h := contDiffOn_integral_of_dominated_joint_jets
    (isOpen_fourierParameterBox b R) (hu.contDiffOn_jointFourierIntegrand hb) hdom
  simpa only [jointFourierIntegrand, jointFourierKernel, fourierVelocity,
    Real.fourier_eq, Circle.smul_def] using h

/-- The original local-Schwartz contract implies genuine joint time and
continuous-frequency C∞ regularity throughout the open preterminal slab. -/
theorem LocalSchwartz.contDiffOn_fourierVelocity {T : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) :
    ContDiffOn ℝ ∞ (fun q : ℝ × Vec => fourierVelocity (u q.1) q.2)
      {q | q.1 ∈ Ioo (0 : ℝ) T} := by
  intro q hq
  let b := (q.1 + T) / 2
  let R := ‖q.2‖ + 1
  have htb : q.1 < b := by dsimp [b]; linarith [hq.2]
  have hbT : b < T := by dsimp [b]; linarith [hq.2]
  have hb : b ∈ Ico (0 : ℝ) T := ⟨(hq.1.trans htb).le, hbT⟩
  have hR : 0 < R := by dsimp [R]; positivity
  have hqbox : q ∈ fourierParameterBox b R := by
    refine ⟨⟨hq.1, htb⟩, ?_⟩
    simp [Metric.mem_ball, R]
  exact ((hu.contDiffOn_fourierVelocity_box hb hR).contDiffAt
    ((isOpen_fourierParameterBox b R).mem_nhds hqbox)).contDiffWithinAt

end

end MethbokeAddon.FDSNR3
