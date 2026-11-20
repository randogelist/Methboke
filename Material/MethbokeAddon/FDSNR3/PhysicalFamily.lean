import MethbokeAddon.FDSNR3.CompactFrequencyInverse
import MethbokeAddon.FDSNR3.JointPacket
import MethbokeAddon.FDSNR3.CrossingDerivative

/-!
# One actual real physical phase family

The compact joint spectrum is inverted only in the frequency variable,
then realified and reassociated into parameter and spacetime coordinates.
The resulting correction is a genuine full joint Schwartz map. Its literal
inverse-integral formula identifies it with the crossing-time construction,
and its regular slices identify it with the previously constructed phase
slice. All physical invariants below concern this same family.

Prepared by static source inspection only. External compiler and named
axiom evidence remain necessary before endpoint acceptance.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate

namespace MethbokeAddon.FDSNR3

noncomputable section

/-- The actual full joint real correction, grouped as `(parameter,(time,space))`. -/
def jointPhysicalCorrection
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    𝓢(ℝ × (ℝ × Vec), Vec) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
    (LinearIsometryEquiv.prodAssoc ℝ ℝ ℝ Vec).symm.toContinuousLinearEquiv
    (SchwartzMap.postcompCLM realifyCLM
      (partialFourierInverse (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ)))

theorem jointPhysicalCorrection_apply
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam t : ℝ) (x : Vec) :
    jointPhysicalCorrection hu hβ hcβ hβsupport hψ hcψ (lam, (t, x)) =
      realify (𝓕⁻ (fun ξ : Vec => jointSpectralCorrection β ψ u ((lam, t), ξ)) x) := by
  change realify (partialFourierInverse
    (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ) ((lam, t), x)) = _
  simp only [partialFourierInverse_apply, jointSpectralSchwartz_apply]

theorem jointPhysicalCorrection_zero_parameter
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (z : ℝ × Vec) :
    jointPhysicalCorrection hu hβ hcβ hβsupport hψ hcψ (0, z) = 0 := by
  rw [jointPhysicalCorrection_apply]
  have hz : (fun ξ : Vec => jointSpectralCorrection β ψ u ((0, z.1), ξ)) = 0 :=
    funext (jointSpectralCorrection_zero_parameter β ψ u z.1)
  simpa only [hz, Real.fourierInv_eq, Pi.zero_apply, smul_zero, integral_zero] using
    (show realify (0 : CVec) = 0 from realifyCLM.map_zero)

def physicalPhaseCorrection
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam : ℝ) : Velocity :=
  fun t x => jointPhysicalCorrection hu hβ hcβ hβsupport hψ hcψ (lam, (t, x))

theorem physicalPhaseCorrection_apply
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam t : ℝ) (x : Vec) :
    physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t x =
      realify (𝓕⁻ (fun ξ : Vec => jointSpectralCorrection β ψ u ((lam, t), ξ)) x) :=
  jointPhysicalCorrection_apply hu hβ hcβ hβsupport hψ hcψ lam t x

theorem physicalPhaseCorrection_eq_inversePhaseCorrection
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam : ℝ} (hlam : |lam| ≤ Real.pi / 4) :
    physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam =
      inversePhaseCorrection β ψ lam u := by
  funext t x
  rw [physicalPhaseCorrection_apply]
  have heq : (fun ξ : Vec => jointSpectralCorrection β ψ u ((lam, t), ξ)) =
      fun ξ : Vec => packetPhaseIncrement β ψ lam t ξ • fourierVelocity (u t) ξ :=
    funext (jointSpectralCorrection_eq_on_small_parameter β ψ u hlam t)
  exact congrArg (fun f : Vec → CVec => realify (𝓕⁻ f x)) heq

theorem physicalPhaseCorrection_zero_parameter
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ 0 = 0 := by
  funext t x
  exact jointPhysicalCorrection_zero_parameter hu hβ hcβ hβsupport hψ hcψ (t, x)

theorem physicalPhaseCorrection_eq_zero_of_beta_zero
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam : ℝ) {t : ℝ} (ht : β t = 0) :
    physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t = 0 := by
  funext x
  rw [physicalPhaseCorrection_apply]
  have hz : (fun ξ : Vec => jointSpectralCorrection β ψ u ((lam, t), ξ)) = 0 :=
    funext (jointSpectralCorrection_eq_zero_of_beta_zero ψ u lam ht)
  simpa only [hz, Real.fourierInv_eq, Pi.zero_apply, smul_zero, integral_zero] using
    (show realify (0 : CVec) = 0 from realifyCLM.map_zero)

theorem physicalPhaseCorrection_tsupport_subset
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam : ℝ) :
    tsupport (physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam) ⊆ tsupport β := by
  apply closure_minimal ?_ (isClosed_tsupport β)
  intro t ht
  by_contra hn
  exact ht (physicalPhaseCorrection_eq_zero_of_beta_zero hu hβ hcβ hβsupport hψ hcψ
    lam (image_eq_zero_of_notMem_tsupport hn))

theorem physicalPhaseCorrection_hasCompactSupport
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam : ℝ) :
    HasCompactSupport (physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam) :=
  hcβ.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (physicalPhaseCorrection_tsupport_subset hu hβ hcβ hβsupport hψ hcψ lam)

/-- A spatial Schwartz representative for the correction at every time and parameter. -/
def physicalCorrectionSlice
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam t : ℝ) :
    𝓢(Vec, Vec) :=
  realSchwartzInverse
    (schwartzRightSlice (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ) (lam, t))

theorem physicalCorrectionSlice_apply
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam t : ℝ) (x : Vec) :
    physicalCorrectionSlice hu hβ hcβ hβsupport hψ hcψ lam t x =
      physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t x := by
  rw [physicalPhaseCorrection_apply]
  change realify (((𝓕⁻ (schwartzRightSlice
    (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ) (lam, t)) :
      𝓢(Vec, CVec)) : Vec → CVec) x) = _
  simp only [SchwartzMap.fourierInv_coe, schwartzRightSlice_coe,
    jointSpectralSchwartz_apply]

theorem physicalCorrectionSlice_coe
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam t : ℝ) :
    (physicalCorrectionSlice hu hβ hcβ hβsupport hψ hcψ lam t : Field) =
      physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t :=
  funext (physicalCorrectionSlice_apply hu hβ hcβ hβsupport hψ hcψ lam t)

theorem fourierVelocity_physicalPhaseCorrection
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ) (lam t : ℝ) (ξ : Vec) :
    fourierVelocity (physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t) ξ =
      jointSpectralCorrection β ψ u ((lam, t), ξ) := by
  rw [← physicalCorrectionSlice_coe hu hβ hcβ hβsupport hψ hcψ lam t]
  exact fourierVelocity_realSchwartzInverse _
    (jointSpectralCorrection_conjugacy hu hβsupport ho lam t) ξ

theorem physicalPhaseCorrection_divergence_free
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ) (lam t : ℝ) :
    ∀ x : Vec,
      divergence (physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t) x = 0 := by
  rw [← physicalCorrectionSlice_coe hu hβ hcβ hβsupport hψ hcψ lam t]
  apply realSchwartzInverse_divergence_free _
    (jointSpectralCorrection_conjugacy hu hβsupport ho lam t)
  intro ξ
  exact jointSpectralCorrection_transverse hu hdiv ψ hβsupport lam t ξ

theorem spectralCorrectionSlice_eq_phase_difference
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) :
    schwartzRightSlice (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ) (lam, t) =
      phaseSpectrum β ψ hψ hcψ lam t (complexifySchwartz (hu.slice ht)) -
        𝓕 (complexifySchwartz (hu.slice ht)) := by
  apply SchwartzMap.ext
  intro ξ
  calc
    schwartzRightSlice (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ)
        (lam, t) ξ = packetPhaseIncrement β ψ lam t ξ • fourierVelocity (u t) ξ :=
      jointSpectralSchwartz_eq_on_small_parameter hu hβ hcβ hβsupport hψ hcψ hlam t ξ
    _ = (phaseSpectrum β ψ hψ hcψ lam t (complexifySchwartz (hu.slice ht)) -
        𝓕 (complexifySchwartz (hu.slice ht))) ξ :=
      (phaseSpectrum_difference_apply β ψ hψ hcψ lam t
        (complexifySchwartz (hu.slice ht)) ξ).symm

theorem physicalCorrectionSlice_eq_phaseSlice_sub
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) :
    physicalCorrectionSlice hu hβ hcβ hβsupport hψ hcψ lam t =
      phaseSlice β ψ hψ hcψ lam t (hu.slice ht) - hu.slice ht := by
  change realifySchwartz (𝓕⁻ (schwartzRightSlice
    (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ) (lam, t))) = _
  rw [spectralCorrectionSlice_eq_phase_difference hu hβ hcβ hβsupport hψ hcψ hlam ht]
  exact (phaseSlice_sub β ψ hψ hcψ lam t (hu.slice ht)).symm

/-- The same seed plus the same globally smooth Schwartz correction. -/
def physicalPhaseFamily
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam : ℝ) : Velocity :=
  u + physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam

theorem physicalPhaseFamily_zero_parameter
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ 0 = u := by
  rw [physicalPhaseFamily, physicalPhaseCorrection_zero_parameter, add_zero]

theorem physicalPhaseFamily_eq_seed_of_beta_zero
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam : ℝ) {t : ℝ} (ht : β t = 0) :
    physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t = u t := by
  change u t + physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t = u t
  rw [physicalPhaseCorrection_eq_zero_of_beta_zero hu hβ hcβ hβsupport hψ hcψ lam ht,
    add_zero]

theorem physicalPhaseFamily_eq_seed_of_time_notMem
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam : ℝ) {t : ℝ} (ht : t ∉ tsupport β) :
    physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t = u t :=
  physicalPhaseFamily_eq_seed_of_beta_zero hu hβ hcβ hβsupport hψ hcψ lam
    (image_eq_zero_of_notMem_tsupport ht)

theorem physicalPhaseFamily_eq_phaseSlice
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) :
    physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t =
      (phaseSlice β ψ hψ hcψ lam t (hu.slice ht) : Field) := by
  funext x
  change u t x + physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t x = _
  rw [← physicalCorrectionSlice_apply hu hβ hcβ hβsupport hψ hcψ lam t x,
    physicalCorrectionSlice_eq_phaseSlice_sub hu hβ hcβ hβsupport hψ hcψ hlam ht]
  change u t x + (phaseSlice β ψ hψ hcψ lam t (hu.slice ht) x - u t x) = _
  abel

theorem physicalPhaseFamily_exists_schwartz_slice
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) :
    ∃ f : 𝓢(Vec, Vec),
      (f : Field) = physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t :=
  ⟨phaseSlice β ψ hψ hcψ lam t (hu.slice ht),
    (physicalPhaseFamily_eq_phaseSlice hu hβ hcβ hβsupport hψ hcψ hlam ht).symm⟩

theorem fourierVelocity_physicalPhaseFamily
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) (ξ : Vec) :
    fourierVelocity (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t) ξ =
      packetPhase β ψ lam t ξ • fourierVelocity (u t) ξ := by
  rw [physicalPhaseFamily_eq_phaseSlice hu hβ hcβ hβsupport hψ hcψ hlam ht]
  exact fourierVelocity_phaseSlice β ψ hψ hcψ ho lam t (hu.slice ht) ξ

theorem physicalPhaseFamily_helicalPower
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T)
    (ξ : Vec) (σ : Fin 2) :
    helicalPower σ (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t) ξ =
      helicalPower σ (u t) ξ := by
  rw [physicalPhaseFamily_eq_phaseSlice hu hβ hcβ hβsupport hψ hcψ hlam ht]
  exact phaseSlice_helicalPower β ψ hψ hcψ ho lam t (hu.slice ht) ξ σ

theorem fourierVelocity_physicalPhaseFamily_eq_of_cutoff_zero
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T)
    {ξ : Vec} (hξ : ψ ξ = 0) :
    fourierVelocity (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t) ξ =
      fourierVelocity (u t) ξ := by
  rw [fourierVelocity_physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ ho hlam ht,
    packetPhase_eq_one_of_psi_zero β lam t hξ, one_smul]

theorem physicalPhaseFamily_divergence_free
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) :
    ∀ x : Vec,
      divergence (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t) x = 0 := by
  rw [physicalPhaseFamily_eq_phaseSlice hu hβ hcβ hβsupport hψ hcψ hlam ht]
  exact phaseSlice_divergence_free β ψ hψ hcψ ho lam t (hu.slice ht) (hdiv t ht)

theorem physicalPhaseFamily_integrable_norm_sq
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) :
    Integrable (fun x : Vec =>
      ‖physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t x‖ ^ 2) volume := by
  rw [physicalPhaseFamily_eq_phaseSlice hu hβ hcβ hβsupport hψ hcψ hlam ht]
  exact schwartz_integrable_norm_sq _

theorem physicalPhaseFamily_energy
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) :
    (∫ x : Vec, ‖physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t x‖ ^ 2) =
      ∫ x : Vec, ‖u t x‖ ^ 2 := by
  rw [physicalPhaseFamily_eq_phaseSlice hu hβ hcβ hβsupport hψ hcψ hlam ht]
  exact phaseSlice_energy β ψ hψ hcψ ho lam t (hu.slice ht)

theorem physicalPhaseFamily_gradientSquare_integrable
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) :
    Integrable
      (gradientSquare (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t)) volume := by
  rw [physicalPhaseFamily_eq_phaseSlice hu hβ hcβ hβsupport hψ hcψ hlam ht]
  exact schwartz_gradientSquare_integrable _

theorem physicalPhaseFamily_dissipation
    {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) :
    dissipation (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t) =
      dissipation (u t) := by
  rw [physicalPhaseFamily_eq_phaseSlice hu hβ hcβ hβsupport hψ hcψ hlam ht]
  exact phaseSlice_dissipation β ψ hψ hcψ ho lam t (hu.slice ht)

end

end MethbokeAddon.FDSNR3
