import MethbokeAddon.FDSNR3.SliceSchwartz
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Fourier.FourierTransformDeriv

/-!
# Dominated smooth parameter integrals for whole-space Fourier analysis

The integration theorem below integrates genuine Taylor jets. Its hypotheses
are measurability and integrable bounds on the actual derivatives of the
integrand; no smoothness conclusion for the integral is assumed.

This source is prepared by static inspection. Acceptance requires matching
external compilation and declaration-level audits.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

section DominatedTaylor

variable {P E A : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace A] {μ : Measure A}

/-- Integration of all actual Taylor jets on an open parameter domain.
The dominating function may depend on the derivative order. -/
theorem integral_hasFTaylorSeriesUpToOn_of_dominated
    {F : P → A → E} {p : A → P → FormalMultilinearSeries ℝ P E}
    {s : Set P} (hs : IsOpen s)
    (hTaylor : ∀ a : A, HasFTaylorSeriesUpToOn ∞ (fun q => F q a) (p a) s)
    (hMeas : ∀ n : ℕ, ∀ q ∈ s, AEStronglyMeasurable (fun a => p a q n) μ)
    (hBound : ∀ n : ℕ, ∃ B : A → ℝ, Integrable B μ ∧
      ∀ a : A, ∀ q ∈ s, ‖p a q n‖ ≤ B a) :
    HasFTaylorSeriesUpToOn ∞ (fun q => ∫ a, F q a ∂μ)
      (fun q n => ∫ a, p a q n ∂μ) s := by
  have hInt : ∀ n : ℕ, ∀ q ∈ s, Integrable (fun a => p a q n) μ := by
    intro n q hq
    obtain ⟨B, hB, hbound⟩ := hBound n
    exact hB.mono' (hMeas n q hq) (ae_of_all _ (fun a => hbound a q hq))
  constructor
  · intro q hq
    calc
      (∫ a, p a q 0 ∂μ).curry0 = ∫ a, (p a q 0).curry0 ∂μ :=
        ((continuousMultilinearCurryFin0 ℝ P E).toLinearIsometry.integral_comp_comm
          (fun a => p a q 0)).symm
      _ = ∫ a, F q a ∂μ :=
        integral_congr_ae (ae_of_all _ (fun a => (hTaylor a).zero_eq q hq))
  · intro n hn q hq
    obtain ⟨B, hB, hbound⟩ := hBound (n + 1)
    have hMeas' : AEStronglyMeasurable (fun a => (p a q (n + 1)).curryLeft) μ :=
      (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (n + 1) => P) E).continuous.comp_aestronglyMeasurable
        (hMeas (n + 1) q hq)
    have hd := hasFDerivAt_integral_of_dominated_of_fderiv_le
      (hs.mem_nhds hq)
      (Filter.Eventually.mono (hs.mem_nhds hq) (fun y hy => hMeas n y hy))
      (hInt n q hq) hMeas'
      (ae_of_all _ (fun a y hy => by
        simpa only [ContinuousMultilinearMap.curryLeft_norm] using hbound a y hy)) hB
      (ae_of_all _ (fun a y hy =>
        ((hTaylor a).fderivWithin n hn y hy).hasFDerivAt (hs.mem_nhds hy)))
    have heq : (∫ a, (p a q (n + 1)).curryLeft ∂μ) =
        (∫ a, p a q (n + 1) ∂μ).curryLeft := by
      have hIntc : Integrable
          (ε := P →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => P) E)
          (fun a : A => by exact! (p a q (n + 1)).curryLeft) μ := by
        apply Integrable.mono'
          (β := P →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin n => P) E) hB
        · simpa using! hMeas'
        · exact ae_of_all _ (fun a => by
            simpa only [ContinuousMultilinearMap.curryLeft_norm] using! hbound a q hq)
      apply ContinuousLinearMap.ext
      intro v
      apply ContinuousMultilinearMap.ext
      intro m
      rw [ContinuousLinearMap.integral_apply hIntc v]
      rw [ContinuousMultilinearMap.integral_apply
        ((ContinuousLinearMap.apply ℝ
          (ContinuousMultilinearMap ℝ (fun _ : Fin n => P) E) v).integrable_comp hIntc) m]
      simpa only [ContinuousMultilinearMap.curryLeft_apply] using
        (ContinuousMultilinearMap.integral_apply (hInt (n + 1) q hq) (Fin.cons v m)).symm
    rw [heq] at hd
    exact hd.hasFDerivWithinAt
  · intro n hn
    obtain ⟨B, hB, hbound⟩ := hBound n
    exact continuousOn_of_dominated (hMeas n)
      (fun q hq => ae_of_all _ (fun a => hbound a q hq)) hB
      (ae_of_all _ (fun a => (hTaylor a).cont n hn))

/-- All orders of differentiation under an integral, expressed solely with
the genuine iterated Fréchet derivatives of the integrand. -/
theorem contDiffOn_integral_of_dominated_iteratedFDerivWithin
    {F : P → A → E} {s : Set P} (hs : IsOpen s)
    (hSmooth : ∀ a : A, ContDiffOn ℝ ∞ (fun q => F q a) s)
    (hMeas : ∀ n : ℕ, ∀ q ∈ s,
      AEStronglyMeasurable
        (fun a => iteratedFDerivWithin ℝ n (fun y => F y a) s q) μ)
    (hBound : ∀ n : ℕ, ∃ B : A → ℝ, Integrable B μ ∧
      ∀ a : A, ∀ q ∈ s,
        ‖iteratedFDerivWithin ℝ n (fun y => F y a) s q‖ ≤ B a) :
    ContDiffOn ℝ ∞ (fun q => ∫ a, F q a ∂μ) s := by
  exact (integral_hasFTaylorSeriesUpToOn_of_dominated hs
    (fun a => (hSmooth a).ftaylorSeriesWithin hs.uniqueDiffOn) hMeas hBound).contDiffOn

end DominatedTaylor

section JointIntegral

variable (P X : Type*)
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Parameter directions, with the integration variable held fixed. -/
def parameterInclusionCLM : P →L[ℝ] (P × X) :=
  (ContinuousLinearMap.id ℝ P).prod (0 : P →L[ℝ] X)

/-- The affine parameter slice through a fixed integration point. -/
def parameterInclusionAffine (x : X) : P →ᴬ[ℝ] (P × X) where
  toFun q := (q, x)
  linear := (parameterInclusionCLM P X).toLinearMap
  map_vadd' := by
    intro r q
    change (q + r, x) = (q, (0 : X)) + (r, x)
    simp
  cont := continuous_id.prodMk continuous_const

@[simp] theorem parameterInclusionAffine_apply (x : X) (q : P) :
    parameterInclusionAffine P X x q = (q, x) := rfl

@[simp] theorem parameterInclusionAffine_contLinear (x : X) :
    (parameterInclusionAffine P X x).contLinear = parameterInclusionCLM P X := by
  ext q <;> rfl

@[simp] theorem parameterInclusionAffine_preimage (x : X) (s : Set P) :
    parameterInclusionAffine P X x ⁻¹' (s ×ˢ (univ : Set X)) = s := by
  ext q
  simp

variable {P X}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace X] [BorelSpace X] [SecondCountableTopology X] {μ : Measure X}

/-- A genuine smooth joint integrand with integrably dominated full jets
gives a smooth parameter integral. In particular, measurability of all
partial jets follows from joint smoothness, rather than being assumed. -/
theorem contDiffOn_integral_of_dominated_joint_jets
    {F : P × X → E} {s : Set P} (hs : IsOpen s)
    (hSmooth : ContDiffOn ℝ ∞ F (s ×ˢ (univ : Set X)))
    (hBound : ∀ n : ℕ, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ q ∈ s, ∀ x : X,
        ‖iteratedFDerivWithin ℝ n F (s ×ˢ univ) (q, x)‖ ≤ B x) :
    ContDiffOn ℝ ∞ (fun q => ∫ x, F (q, x) ∂μ) s := by
  let p : X → P → FormalMultilinearSeries ℝ P E := fun x q n =>
    (iteratedFDerivWithin ℝ n F (s ×ˢ univ) (q, x)).compContinuousLinearMap
      (fun _ : Fin n => parameterInclusionCLM P X)
  have hTaylor : ∀ x : X,
      HasFTaylorSeriesUpToOn ∞ (fun q => F (q, x)) (p x) s := by
    intro x
    have h := (hSmooth.ftaylorSeriesWithin (hs.prod isOpen_univ).uniqueDiffOn).comp_continuousAffineMap
      (parameterInclusionAffine P X x)
    simpa only [parameterInclusionAffine_preimage, parameterInclusionAffine_apply,
      parameterInclusionAffine_contLinear, Function.comp_def, ftaylorSeriesWithin, p] using h
  have hMeas : ∀ n : ℕ, ∀ q ∈ s, AEStronglyMeasurable (fun x => p x q n) μ := by
    intro n q hq
    have hn : (n : ℕ∞ω) ≤ ∞ := by
      exact_mod_cast (le_top : (n : ℕ∞) ≤ ⊤)
    have hc : Continuous (fun x : X =>
        iteratedFDerivWithin ℝ n F (s ×ˢ univ) (q, x)) :=
      (hSmooth.continuousOn_iteratedFDerivWithin hn (hs.prod isOpen_univ).uniqueDiffOn).comp_continuous
        (continuous_const.prodMk continuous_id) (fun x => ⟨hq, mem_univ x⟩)
    exact ((ContinuousMultilinearMap.compContinuousLinearMapL
      (fun _ : Fin n => parameterInclusionCLM P X)).continuous.comp hc).aestronglyMeasurable
  have hDom : ∀ n : ℕ, ∃ B : X → ℝ, Integrable B μ ∧
      ∀ x : X, ∀ q ∈ s, ‖p x q n‖ ≤ B x := by
    intro n
    obtain ⟨B, hB, hbound⟩ := hBound n
    refine ⟨fun x => B x * ‖parameterInclusionCLM P X‖ ^ n,
      hB.mul_const _, ?_⟩
    intro x q hq
    exact ((iteratedFDerivWithin ℝ n F (s ×ˢ univ) (q, x)).norm_compContinuousLinearMap_le
      (fun _ : Fin n => parameterInclusionCLM P X)).trans (by
        simpa using (mul_le_mul_of_nonneg_right (hbound q hq x)
          (pow_nonneg (norm_nonneg (parameterInclusionCLM P X)) n)))
  exact (integral_hasFTaylorSeriesUpToOn_of_dominated hs hTaylor hMeas hDom).contDiffOn

end JointIntegral

section FourierContinuity

/-- Every derivative order in the original local-Schwartz contract has
a uniform inverse-polynomial bound on each closed preterminal slab. -/
theorem LocalSchwartz.uniform_jet_decay {T b : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) (N n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) b, ∀ x : Vec,
      ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x)‖ ≤ C * (1 + ‖x‖) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := hu.2 b hb N n
  refine ⟨C, hC, ?_⟩
  intro t ht x
  have hpos : 0 < (1 + ‖x‖) ^ N := by positivity
  have h := hbound t ht x
  change (1 + ‖x‖) ^ N *
    ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T) (t, x)‖ ≤ C at h
  calc
    ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x)‖ ≤ C / (1 + ‖x‖) ^ N :=
      (le_div_iff₀ hpos).mpr (by simpa only [mul_comm] using h)
    _ = C * (1 + ‖x‖) ^ (-(N : ℝ)) := by
      rw [Real.rpow_neg (by positivity), Real.rpow_natCast]
      rfl

/-- Joint time-frequency continuity, with the original one-sided initial
boundary included. The only domination used is the actual zeroth jet. -/
theorem LocalSchwartz.continuousOn_fourierVelocity_slab {T b : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) :
    ContinuousOn (fun q : ℝ × Vec => fourierVelocity (u q.1) q.2)
      {q | q.1 ∈ Icc (0 : ℝ) b} := by
  let m := (volume : Measure Vec).integrablePower
  obtain ⟨C, hC, hbound⟩ := hu.uniform_jet_decay hb m 0
  have hvalue : ∀ t ∈ Icc (0 : ℝ) b, ∀ x : Vec,
      ‖u t x‖ ≤ C * (1 + ‖x‖) ^ (-(m : ℝ)) := by
    simpa only [norm_iteratedFDerivWithin_zero] using hbound
  have htime : ∀ q : ℝ × Vec, q.1 ∈ Icc (0 : ℝ) b →
      q.1 ∈ Ico (0 : ℝ) T :=
    fun q hq => ⟨hq.1, lt_of_le_of_lt hq.2 hb.2⟩
  have hc : ContinuousOn
      (fun q : ℝ × Vec => ∫ x : Vec,
        Real.fourierChar (-inner ℝ x q.2) • complexify (u q.1 x))
      {q | q.1 ∈ Icc (0 : ℝ) b} := by
    apply continuousOn_of_dominated
      (bound := fun x : Vec => C * (1 + ‖x‖) ^ (-(m : ℝ)))
    · intro q hq
      have hi : Integrable (fun x : Vec => complexify (u q.1 x)) :=
        (complexifySchwartz (hu.slice (htime q hq))).integrable
      exact ((Real.fourierIntegral_convergent_iff q.2).mpr hi).aestronglyMeasurable
    · intro q hq
      exact ae_of_all _ (fun x => by
        simpa only [Circle.norm_smul, norm_complexify] using hvalue q.1 hq x)
    · exact ((volume : Measure Vec).integrable_pow_neg_integrablePower).const_mul C
    · apply ae_of_all
      intro x
      have hux : ContinuousOn (fun q : ℝ × Vec => u q.1 x)
          {q | q.1 ∈ Icc (0 : ℝ) b} :=
        hu.1.continuousOn.comp (continuous_fst.prodMk continuous_const).continuousOn
          (fun q hq => htime q hq)
      exact (Real.continuous_fourierChar.comp (by fun_prop)).continuousOn.smul
        (complexifyCLM.continuous.comp_continuousOn hux)
  simpa only [fourierVelocity, Real.fourier_eq] using hc

/-- The actual Fourier field is jointly continuous at every positive
preterminal time and every frequency. -/
theorem LocalSchwartz.continuousAt_fourierVelocity {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) (ξ : Vec) :
    ContinuousAt (fun q : ℝ × Vec => fourierVelocity (u q.1) q.2) (t, ξ) := by
  let b := (t + T) / 2
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have hb : b ∈ Ico (0 : ℝ) T := ⟨(ht.1.trans htb).le, hbT⟩
  apply (hu.continuousOn_fourierVelocity_slab hb (t, ξ) ⟨ht.1.le, htb.le⟩).continuousAt
  exact continuous_fst.continuousAt.preimage_mem_nhds (Icc_mem_nhds ht.1 htb)

/-- The early time-continuity leaf used to retain a nonzero Fourier
component while choosing the phase's zero-crossing time. -/
theorem LocalSchwartz.continuousAt_fourier_time {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) (ξ : Vec) :
    ContinuousAt (fun r : ℝ => fourierVelocity (u r) ξ) t :=
  (hu.continuousAt_fourierVelocity ht ξ).comp (f := fun r : ℝ => (r, ξ))
    (continuousAt_id.prodMk continuousAt_const)

end FourierContinuity

section FourierTimeDerivative

theorem preterminalSpacetime_mem_nhds {T t : ℝ}
    (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    preterminalSpacetime T ∈ 𝓝 (t, x) := by
  exact continuous_fst.continuousAt.preimage_mem_nhds
    (Ico_mem_nhds ht.1 ht.2)

/-- The native temporal derivative is the time direction of the actual
joint derivative at an interior preterminal time. -/
theorem preterminal_hasDerivAt_time_joint {T t : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    HasDerivAt (fun r : ℝ => u r x)
      (fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x) (1, 0)) t := by
  have htime : (t, x) ∈ preterminalSpacetime T := ⟨ht.1.le, ht.2⟩
  have hderiv := (hu.differentiableOn (by simp) (t, x) htime).hasFDerivWithinAt.hasFDerivAt
    (preterminalSpacetime_mem_nhds ht x)
  exact hderiv.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t x))

theorem preterminal_timeDerivative_eq_joint {T t : ℝ} {u : Velocity}
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (preterminalSpacetime T))
    (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    timeDerivative u t x =
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x) (1, 0) := by
  rw [timeDerivative, derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)]
  exact (preterminal_hasDerivAt_time_joint hu ht x).deriv

theorem LocalSchwartz.hasDerivAt_time {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) (x : Vec) :
    HasDerivAt (fun r : ℝ => u r x) (timeDerivative u t x) t := by
  rw [preterminal_timeDerivative_eq_joint hu.1 ht x]
  exact preterminal_hasDerivAt_time_joint hu.1 ht x

theorem LocalSchwartz.continuous_timeDerivative_slice {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) :
    Continuous (timeDerivative u t) := by
  have hone : (1 : ℕ∞ω) ≤ ∞ := by
    exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
  have hc : Continuous (fun x : Vec =>
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x)) :=
    (hu.1.continuousOn_fderivWithin (uniqueDiffOn_preterminalSpacetime T) hone).comp_continuous
      (continuous_const.prodMk continuous_id)
      (fun x => show (t, x) ∈ preterminalSpacetime T from ⟨ht.1.le, ht.2⟩)
  have heq : timeDerivative u t = fun x : Vec =>
      fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
        (preterminalSpacetime T) (t, x) (1, 0) :=
    funext (preterminal_timeDerivative_eq_joint hu.1 ht)
  rw [heq]
  exact hc.clm_apply continuous_const

theorem LocalSchwartz.uniform_timeDerivative_decay {T b : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (hb : b ∈ Ico (0 : ℝ) T) (N : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo (0 : ℝ) b, ∀ x : Vec,
      ‖timeDerivative u t x‖ ≤ C * (1 + ‖x‖) ^ (-(N : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := hu.uniform_jet_decay hb N 1
  refine ⟨C, hC, ?_⟩
  intro t ht x
  have htT : t ∈ Ioo (0 : ℝ) T := ⟨ht.1, ht.2.trans hb.2⟩
  have hm : (t, x) ∈ preterminalSpacetime T := ⟨ht.1.le, htT.2⟩
  rw [preterminal_timeDerivative_eq_joint hu.1 htT x]
  have h := hbound t ⟨ht.1.le, ht.2.le⟩ x
  rw [norm_iteratedFDerivWithin_one _
    (uniqueDiffOn_preterminalSpacetime T (t, x) hm)] at h
  exact ((fderivWithin ℝ (fun z : ℝ × Vec => u z.1 z.2)
    (preterminalSpacetime T) (t, x)).le_opNorm (1, 0)).trans
      (by simpa only [Prod.norm_def, norm_one, norm_zero, max_eq_left zero_le_one, mul_one]
        using h)

theorem LocalSchwartz.timeDerivative_integrable {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) :
    Integrable (timeDerivative u t) := by
  let b := (t + T) / 2
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have hb : b ∈ Ico (0 : ℝ) T := ⟨(ht.1.trans htb).le, hbT⟩
  obtain ⟨C, _, hC⟩ := hu.uniform_timeDerivative_decay hb
    (volume : Measure Vec).integrablePower
  exact (((volume : Measure Vec).integrable_pow_neg_integrablePower).const_mul C).mono'
    (hu.continuous_timeDerivative_slice ht).aestronglyMeasurable
    (ae_of_all _ (fun x => hC t ⟨ht.1, htb⟩ x))

/-- The first genuine parameter derivative commutes with the actual
whole-space Fourier integral. The output uses the native temporal
derivative, whose initial definition is one-sided. -/
theorem LocalSchwartz.hasDerivAt_fourier_time {T t : ℝ} {u : Velocity}
    (hu : LocalSchwartz T u) (ht : t ∈ Ioo (0 : ℝ) T) (ξ : Vec) :
    HasDerivAt (fun r : ℝ => fourierVelocity (u r) ξ)
      (fourierVelocity (timeDerivative u t) ξ) t := by
  let b := (t + T) / 2
  have htb : t < b := by dsimp [b]; linarith [ht.2]
  have hbT : b < T := by dsimp [b]; linarith [ht.2]
  have hb : b ∈ Ico (0 : ℝ) T := ⟨(ht.1.trans htb).le, hbT⟩
  let m := (volume : Measure Vec).integrablePower
  obtain ⟨C, _, hC⟩ := hu.uniform_timeDerivative_decay hb m
  have htime : ∀ r ∈ Ioo (0 : ℝ) b, r ∈ Ioo (0 : ℝ) T :=
    fun r hr => ⟨hr.1, hr.2.trans hbT⟩
  have hInt : ∀ r ∈ Ioo (0 : ℝ) b, Integrable (fun x : Vec =>
      Real.fourierChar (-inner ℝ x ξ) • complexify (u r x)) := by
    intro r hr
    exact (Real.fourierIntegral_convergent_iff ξ).mpr
      (complexifySchwartz (hu.slice ⟨hr.1.le, (htime r hr).2⟩)).integrable
  have hInt' : Integrable (fun x : Vec =>
      Real.fourierChar (-inner ℝ x ξ) • complexify (timeDerivative u t x)) :=
    (Real.fourierIntegral_convergent_iff ξ).mpr
      (complexifyCLM.integrable_comp (hu.timeDerivative_integrable ht))
  have hdiff : ∀ᵐ x : Vec, ∀ r ∈ Ioo (0 : ℝ) b,
      HasDerivAt (fun r : ℝ =>
        Real.fourierChar (-inner ℝ x ξ) • complexify (u r x))
        (Real.fourierChar (-inner ℝ x ξ) • complexify (timeDerivative u r x)) r := by
    apply ae_of_all
    intro x r hr
    change HasDerivAt (fun r : ℝ => (Real.fourierChar (-inner ℝ x ξ) : ℂ) •
      complexify (u r x))
      ((Real.fourierChar (-inner ℝ x ξ) : ℂ) • complexify (timeDerivative u r x)) r
    exact (complexifyCLM.hasFDerivAt.comp_hasDerivAt r
      (hu.hasDerivAt_time (htime r hr) x)).const_smul
        (Real.fourierChar (-inner ℝ x ξ) : ℂ)
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds ht.1 htb)
    (Filter.Eventually.mono (Ioo_mem_nhds ht.1 htb)
      (fun r hr => (hInt r hr).aestronglyMeasurable))
    (hInt t ⟨ht.1, htb⟩) hInt'.aestronglyMeasurable
    (ae_of_all _ (fun x r hr => by
      simpa only [Circle.norm_smul, norm_complexify] using hC r hr x))
    (((volume : Measure Vec).integrable_pow_neg_integrablePower).const_mul C)
    hdiff).2
  simpa only [fourierVelocity, Real.fourier_eq] using hd

end FourierTimeDerivative

end

end MethbokeAddon.FDSNR3
