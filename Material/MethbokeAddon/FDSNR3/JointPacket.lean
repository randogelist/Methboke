import MethbokeAddon.FDSNR3.ForwardFourierSmooth
import MethbokeAddon.FDSNR3.Phase
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct

/-!
# One actual compact spectral correction for the whole parameter family

The parameter cutoff equals one on the entire requested closed parameter
range. The time and frequency factors make the correction vanish outside
their compact carriers. The literal expression is already zero outside the
preterminal slab, so no extension theorem or assumed Fourier regularity is
needed to construct its genuine joint Schwartz representative.

Prepared without local Lean execution. External compiler and named axiom
evidence are required for acceptance.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

def phaseParameterBump : ContDiffBump (0 : ℝ) where
  rIn := Real.pi / 4
  rOut := Real.pi / 2
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith [Real.pi_pos]

def phaseParameterCutoff (lam : ℝ) : ℝ := phaseParameterBump lam

theorem phaseParameterCutoff_contDiff : ContDiff ℝ ∞ phaseParameterCutoff :=
  phaseParameterBump.contDiff

theorem phaseParameterCutoff_hasCompactSupport : HasCompactSupport phaseParameterCutoff :=
  phaseParameterBump.hasCompactSupport

theorem phaseParameterCutoff_eq_one {lam : ℝ} (hlam : |lam| ≤ Real.pi / 4) :
    phaseParameterCutoff lam = 1 := by
  apply phaseParameterBump.one_of_mem_closedBall
  simpa only [Metric.mem_closedBall, Real.dist_eq, sub_zero, phaseParameterBump] using hlam

/-- The actual spectrum of the physical correction. Its grouping agrees
with the partial inverse Fourier transform: `((parameter,time),frequency)`. -/
def jointSpectralCorrection (β : ℝ → ℝ) (ψ : Vec → ℝ) (u : Velocity)
    (z : (ℝ × ℝ) × Vec) : CVec :=
  phaseParameterCutoff z.1.1 •
    (packetPhaseIncrement β ψ z.1.1 z.1.2 z.2 • fourierVelocity (u z.1.2) z.2)

@[simp] theorem jointSpectralCorrection_zero_parameter
    (β : ℝ → ℝ) (ψ : Vec → ℝ) (u : Velocity) (t : ℝ) (ξ : Vec) :
    jointSpectralCorrection β ψ u ((0, t), ξ) = 0 := by
  simp [jointSpectralCorrection]

theorem jointSpectralCorrection_eq_zero_of_parameterCutoff_zero
    (β : ℝ → ℝ) (ψ : Vec → ℝ) (u : Velocity) {lam : ℝ}
    (hlam : phaseParameterCutoff lam = 0) (t : ℝ) (ξ : Vec) :
    jointSpectralCorrection β ψ u ((lam, t), ξ) = 0 := by
  simp [jointSpectralCorrection, hlam]

theorem jointSpectralCorrection_eq_zero_of_beta_zero
    {β : ℝ → ℝ} (ψ : Vec → ℝ) (u : Velocity) (lam : ℝ) {t : ℝ}
    (hβ : β t = 0) (ξ : Vec) :
    jointSpectralCorrection β ψ u ((lam, t), ξ) = 0 := by
  simp [jointSpectralCorrection, packetPhaseIncrement,
    packetPhase_eq_one_of_beta_zero ψ lam hβ]

theorem jointSpectralCorrection_eq_zero_of_psi_zero
    (β : ℝ → ℝ) {ψ : Vec → ℝ} (u : Velocity) (lam t : ℝ) {ξ : Vec}
    (hψ : ψ ξ = 0) :
    jointSpectralCorrection β ψ u ((lam, t), ξ) = 0 := by
  simp [jointSpectralCorrection, packetPhaseIncrement,
    packetPhase_eq_one_of_psi_zero β lam t hψ]

theorem jointSpectralCorrection_eq_on_small_parameter
    (β : ℝ → ℝ) (ψ : Vec → ℝ) (u : Velocity) {lam : ℝ}
    (hlam : |lam| ≤ Real.pi / 4) (t : ℝ) (ξ : Vec) :
    jointSpectralCorrection β ψ u ((lam, t), ξ) =
      packetPhaseIncrement β ψ lam t ξ • fourierVelocity (u t) ξ := by
  simp only [jointSpectralCorrection, phaseParameterCutoff_eq_one hlam, one_smul]

theorem jointSpectralCorrection_eq_zero_of_time_notMem
    {β : ℝ → ℝ} (ψ : Vec → ℝ) (u : Velocity) {J : Set ℝ}
    (hβsupport : tsupport β ⊆ J) (lam : ℝ) {t : ℝ} (ht : t ∉ J) (ξ : Vec) :
    jointSpectralCorrection β ψ u ((lam, t), ξ) = 0 := by
  apply jointSpectralCorrection_eq_zero_of_beta_zero ψ u lam
  exact image_eq_zero_of_notMem_tsupport (fun h => ht (hβsupport h))

theorem jointSpectralCorrection_tsupport_subset
    (β : ℝ → ℝ) (ψ : Vec → ℝ) (u : Velocity) :
    tsupport (jointSpectralCorrection β ψ u) ⊆
      (tsupport phaseParameterCutoff ×ˢ tsupport β) ×ˢ tsupport ψ := by
  apply closure_minimal ?_
    (((isClosed_tsupport phaseParameterCutoff).prod (isClosed_tsupport β)).prod
      (isClosed_tsupport ψ))
  intro z hz
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · by_contra hlam
    exact hz (jointSpectralCorrection_eq_zero_of_parameterCutoff_zero β ψ u
      (image_eq_zero_of_notMem_tsupport hlam) z.1.2 z.2)
  · by_contra ht
    exact hz (jointSpectralCorrection_eq_zero_of_beta_zero ψ u z.1.1
      (image_eq_zero_of_notMem_tsupport ht) z.2)
  · by_contra hξ
    exact hz (jointSpectralCorrection_eq_zero_of_psi_zero β u z.1.1 z.1.2
      (image_eq_zero_of_notMem_tsupport hξ))

theorem jointSpectralCorrection_hasCompactSupport
    {β : ℝ → ℝ} {ψ : Vec → ℝ} (u : Velocity)
    (hβ : HasCompactSupport β) (hψ : HasCompactSupport ψ) :
    HasCompactSupport (jointSpectralCorrection β ψ u) :=
  ((phaseParameterCutoff_hasCompactSupport.isCompact.prod hβ.isCompact).prod hψ.isCompact).of_isClosed_subset
    (isClosed_tsupport _) (jointSpectralCorrection_tsupport_subset β ψ u)

theorem jointSpectralCorrection_contDiff
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hψ : ContDiff ℝ ∞ ψ)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (jointSpectralCorrection β ψ u) := by
  have hparam : ContDiff ℝ ∞
      (fun z : (ℝ × ℝ) × Vec => phaseParameterCutoff z.1.1) :=
    phaseParameterCutoff_contDiff.comp (contDiff_fst.comp contDiff_fst)
  have hphase : ContDiff ℝ ∞
      (fun z : (ℝ × ℝ) × Vec => packetPhaseIncrement β ψ z.1.1 z.1.2 z.2) :=
    ((MethbokeAddon.FDSN.contDiff_phase.comp
      (((contDiff_fst.comp contDiff_fst).mul
        (hβ.comp (contDiff_snd.comp contDiff_fst))).mul
          (hψ.comp contDiff_snd))).sub contDiff_const)
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases ht : z.1.2 ∈ tsupport β
  · have htT := hβsupport ht
    have hnhds : {q : ℝ × Vec | q.1 ∈ Ioo (0 : ℝ) T} ∈ 𝓝 (z.1.2, z.2) :=
      continuous_fst.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds htT)
    have hfourier : ContDiffAt ℝ ∞
        (fun y : (ℝ × ℝ) × Vec => fourierVelocity (u y.1.2) y.2) z :=
      ContDiffAt.comp
        (f := fun y : (ℝ × ℝ) × Vec => (y.1.2, y.2))
        (g := fun q : ℝ × Vec => fourierVelocity (u q.1) q.2) z
        (hu.contDiffOn_fourierVelocity.contDiffAt hnhds)
        (((contDiff_snd.comp contDiff_fst).prodMk contDiff_snd).contDiffAt)
    exact hparam.contDiffAt.smul (hphase.contDiffAt.smul hfourier)
  · have hzero : jointSpectralCorrection β ψ u =ᶠ[𝓝 z]
        (fun _ : (ℝ × ℝ) × Vec => (0 : CVec)) := by
      have hnear : ∀ᶠ y : (ℝ × ℝ) × Vec in 𝓝 z, y.1.2 ∉ tsupport β :=
        (((isClosed_tsupport β).isOpen_compl.preimage
          (continuous_snd.comp continuous_fst)).mem_nhds ht)
      filter_upwards [hnear] with y hy
      exact jointSpectralCorrection_eq_zero_of_beta_zero ψ u y.1.1
        (image_eq_zero_of_notMem_tsupport hy) y.2
    exact contDiffAt_const.congr_of_eventuallyEq hzero

/-- Realness of the original physical slices and oddness of the frequency
phase give Hermitian symmetry for this same global spectrum. -/
theorem jointSpectralCorrection_conjugacy
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψodd : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) (ξ : Vec) (i : Fin 3) :
    jointSpectralCorrection β ψ u ((lam, t), -ξ) i =
      conj (jointSpectralCorrection β ψ u ((lam, t), ξ) i) := by
  by_cases ht : t ∈ tsupport β
  · have htT := hβsupport ht
    have hf : fourierVelocity (u t) (-ξ) i = conj (fourierVelocity (u t) ξ i) :=
      fourierVelocity_conjugacy (hu.slice ⟨htT.1.le, htT.2⟩) ξ i
    have hp : packetPhaseIncrement β ψ lam t (-ξ) =
        conj (packetPhaseIncrement β ψ lam t ξ) := by
      simp only [packetPhaseIncrement, packetPhase_neg β hψodd lam t ξ, map_sub, map_one]
    change (phaseParameterCutoff lam : ℂ) *
        (packetPhaseIncrement β ψ lam t (-ξ) * fourierVelocity (u t) (-ξ) i) =
      conj ((phaseParameterCutoff lam : ℂ) *
        (packetPhaseIncrement β ψ lam t ξ * fourierVelocity (u t) ξ i))
    rw [hp, hf]
    simp only [map_mul, Complex.conj_ofReal]
  · have hβzero : β t = 0 := image_eq_zero_of_notMem_tsupport ht
    rw [jointSpectralCorrection_eq_zero_of_beta_zero ψ u lam hβzero (-ξ),
      jointSpectralCorrection_eq_zero_of_beta_zero ψ u lam hβzero ξ]
    simp

/-- Solenoidality is retained by the actual compact joint correction
spectrum, including times outside the deformation carrier. -/
theorem jointSpectralCorrection_transverse
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0)
    {β : ℝ → ℝ} (ψ : Vec → ℝ)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (lam t : ℝ) (ξ : Vec) :
    ∑ i : Fin 3, (ξ i : ℂ) * jointSpectralCorrection β ψ u ((lam, t), ξ) i = 0 := by
  by_cases ht : t ∈ tsupport β
  · have htT := hβsupport ht
    have htime : t ∈ Ico (0 : ℝ) T := ⟨htT.1.le, htT.2⟩
    have hf : ∑ i : Fin 3, (ξ i : ℂ) * fourierVelocity (u t) ξ i = 0 :=
      fourierVelocity_divergence_free (hu.slice htime) (hdiv t htime) ξ
    change (∑ i : Fin 3, (ξ i : ℂ) * ((phaseParameterCutoff lam : ℂ) *
      (packetPhaseIncrement β ψ lam t ξ * fourierVelocity (u t) ξ i))) = 0
    calc
      (∑ i : Fin 3, (ξ i : ℂ) * ((phaseParameterCutoff lam : ℂ) *
          (packetPhaseIncrement β ψ lam t ξ * fourierVelocity (u t) ξ i))) =
          ((phaseParameterCutoff lam : ℂ) * packetPhaseIncrement β ψ lam t ξ) *
            (∑ i : Fin 3, (ξ i : ℂ) * fourierVelocity (u t) ξ i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0 := by rw [hf, mul_zero]
  · rw [jointSpectralCorrection_eq_zero_of_beta_zero ψ u lam
      (image_eq_zero_of_notMem_tsupport ht) ξ]
    simp

/-- The actual compact spectral correction is admitted to full joint
Schwartz space, with no new analytic hypothesis on the seed. -/
def jointSpectralSchwartz
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    𝓢((ℝ × ℝ) × Vec, CVec) :=
  (jointSpectralCorrection_hasCompactSupport u hcβ hcψ).toSchwartzMap
    (jointSpectralCorrection_contDiff hu hβ hψ hβsupport)

@[simp] theorem jointSpectralSchwartz_apply
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (z : (ℝ × ℝ) × Vec) :
    jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ z =
      jointSpectralCorrection β ψ u z := rfl

@[simp] theorem jointSpectralSchwartz_zero_parameter
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (t : ℝ) (ξ : Vec) :
    jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ ((0, t), ξ) = 0 := by
  exact jointSpectralCorrection_zero_parameter β ψ u t ξ

theorem jointSpectralSchwartz_eq_on_small_parameter
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam : ℝ} (hlam : |lam| ≤ Real.pi / 4) (t : ℝ) (ξ : Vec) :
    jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ ((lam, t), ξ) =
      packetPhaseIncrement β ψ lam t ξ • fourierVelocity (u t) ξ :=
  jointSpectralCorrection_eq_on_small_parameter β ψ u hlam t ξ

theorem jointSpectralSchwartz_tsupport_subset
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    tsupport (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ) ⊆
      (tsupport phaseParameterCutoff ×ˢ tsupport β) ×ˢ tsupport ψ :=
  jointSpectralCorrection_tsupport_subset β ψ u

end

end MethbokeAddon.FDSNR3
