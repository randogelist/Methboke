import FDSNR3PhysicalFamily.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

noncomputable section
open Set MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ContDiff FourierTransform SchwartzMap ComplexConjugate

example {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) :
    jointPhysicalCorrection hu hβ hcβ hβsupport hψ hcψ =
      SchwartzMap.compCLMOfContinuousLinearEquiv ℝ
        (LinearIsometryEquiv.prodAssoc ℝ ℝ ℝ Vec).symm.toContinuousLinearEquiv
        (SchwartzMap.postcompCLM realifyCLM
          (partialFourierInverse (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ))) := rfl

example {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam : ℝ) :
    physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam =
      fun t x => jointPhysicalCorrection hu hβ hcβ hβsupport hψ hcψ (lam, (t, x)) := rfl

example {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam t : ℝ) :
    physicalCorrectionSlice hu hβ hcβ hβsupport hψ hcψ lam t =
      realSchwartzInverse
        (schwartzRightSlice (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ) (lam, t)) := rfl

example {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam : ℝ) :
    physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam =
      u + physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam := rfl

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam t : ℝ) (x : Vec),
    jointPhysicalCorrection hu hβ hcβ hβsupport hψ hcψ (lam, (t, x)) =
      realify (𝓕⁻ (fun ξ : Vec => jointSpectralCorrection β ψ u ((lam, t), ξ)) x) :=
  @jointPhysicalCorrection_apply

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (z : ℝ × Vec),
    jointPhysicalCorrection hu hβ hcβ hβsupport hψ hcψ (0, z) = 0 :=
  @jointPhysicalCorrection_zero_parameter

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam t : ℝ) (x : Vec),
    physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t x =
      realify (𝓕⁻ (fun ξ : Vec => jointSpectralCorrection β ψ u ((lam, t), ξ)) x) :=
  @physicalPhaseCorrection_apply

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam : ℝ} (hlam : |lam| ≤ Real.pi / 4),
    physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam =
      inversePhaseCorrection β ψ lam u :=
  @physicalPhaseCorrection_eq_inversePhaseCorrection

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
    physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ 0 = 0 :=
  @physicalPhaseCorrection_zero_parameter

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam : ℝ) {t : ℝ} (ht : β t = 0),
    physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t = 0 :=
  @physicalPhaseCorrection_eq_zero_of_beta_zero

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam : ℝ),
    tsupport (physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam) ⊆ tsupport β :=
  @physicalPhaseCorrection_tsupport_subset

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam : ℝ),
    HasCompactSupport (physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam) :=
  @physicalPhaseCorrection_hasCompactSupport

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam t : ℝ) (x : Vec),
    physicalCorrectionSlice hu hβ hcβ hβsupport hψ hcψ lam t x =
      physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t x :=
  @physicalCorrectionSlice_apply

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ) (lam t : ℝ),
    (physicalCorrectionSlice hu hβ hcβ hβsupport hψ hcψ lam t : Field) =
      physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t :=
  @physicalCorrectionSlice_coe

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ) (lam t : ℝ) (ξ : Vec),
    fourierVelocity (physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t) ξ =
      jointSpectralCorrection β ψ u ((lam, t), ξ) :=
  @fourierVelocity_physicalPhaseCorrection

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ) (lam t : ℝ),
    ∀ x : Vec,
      divergence (physicalPhaseCorrection hu hβ hcβ hβsupport hψ hcψ lam t) x = 0 :=
  @physicalPhaseCorrection_divergence_free

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T),
    schwartzRightSlice (jointSpectralSchwartz hu hβ hcβ hβsupport hψ hcψ) (lam, t) =
      phaseSpectrum β ψ hψ hcψ lam t (complexifySchwartz (hu.slice ht)) -
        𝓕 (complexifySchwartz (hu.slice ht)) :=
  @spectralCorrectionSlice_eq_phase_difference

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T),
    physicalCorrectionSlice hu hβ hcβ hβsupport hψ hcψ lam t =
      phaseSlice β ψ hψ hcψ lam t (hu.slice ht) - hu.slice ht :=
  @physicalCorrectionSlice_eq_phaseSlice_sub

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ),
    physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ 0 = u :=
  @physicalPhaseFamily_zero_parameter

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam : ℝ) {t : ℝ} (ht : β t = 0),
    physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t = u t :=
  @physicalPhaseFamily_eq_seed_of_beta_zero

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (lam : ℝ) {t : ℝ} (ht : t ∉ tsupport β),
    physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t = u t :=
  @physicalPhaseFamily_eq_seed_of_time_notMem

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T),
    physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t =
      (phaseSlice β ψ hψ hcψ lam t (hu.slice ht) : Field) :=
  @physicalPhaseFamily_eq_phaseSlice

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T),
    ∃ f : 𝓢(Vec, Vec),
      (f : Field) = physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t :=
  @physicalPhaseFamily_exists_schwartz_slice

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T) (ξ : Vec),
    fourierVelocity (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t) ξ =
      packetPhase β ψ lam t ξ • fourierVelocity (u t) ξ :=
  @fourierVelocity_physicalPhaseFamily

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T)
    (ξ : Vec) (σ : Fin 2),
    helicalPower σ (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t) ξ =
      helicalPower σ (u t) ξ :=
  @physicalPhaseFamily_helicalPower

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T)
    {ξ : Vec} (hξ : ψ ξ = 0),
    fourierVelocity (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t) ξ =
      fourierVelocity (u t) ξ :=
  @fourierVelocity_physicalPhaseFamily_eq_of_cutoff_zero

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    (hdiv : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T),
    ∀ x : Vec,
      divergence (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t) x = 0 :=
  @physicalPhaseFamily_divergence_free

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T),
    Integrable (fun x : Vec =>
      ‖physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t x‖ ^ 2) volume :=
  @physicalPhaseFamily_integrable_norm_sq

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T),
    (∫ x : Vec, ‖physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t x‖ ^ 2) =
      ∫ x : Vec, ‖u t x‖ ^ 2 :=
  @physicalPhaseFamily_energy

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T),
    Integrable
      (gradientSquare (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t)) volume :=
  @physicalPhaseFamily_gradientSquare_integrable

example : ∀ {T : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} {ψ : Vec → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hcβ : HasCompactSupport β)
    (hβsupport : tsupport β ⊆ Ioo (0 : ℝ) T)
    (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    {lam t : ℝ} (hlam : |lam| ≤ Real.pi / 4) (ht : t ∈ Ico (0 : ℝ) T),
    dissipation (physicalPhaseFamily hu hβ hcβ hβsupport hψ hcψ lam t) =
      dissipation (u t) :=
  @physicalPhaseFamily_dissipation

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointPhysicalCorrection"
#check @MethbokeAddon.FDSNR3.jointPhysicalCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointPhysicalCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointPhysicalCorrection"
#print axioms MethbokeAddon.FDSNR3.jointPhysicalCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointPhysicalCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointPhysicalCorrection_apply"
#check @MethbokeAddon.FDSNR3.jointPhysicalCorrection_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointPhysicalCorrection_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointPhysicalCorrection_apply"
#print axioms MethbokeAddon.FDSNR3.jointPhysicalCorrection_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointPhysicalCorrection_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.jointPhysicalCorrection_zero_parameter"
#check @MethbokeAddon.FDSNR3.jointPhysicalCorrection_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.jointPhysicalCorrection_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.jointPhysicalCorrection_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.jointPhysicalCorrection_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.jointPhysicalCorrection_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection"
#check @MethbokeAddon.FDSNR3.physicalPhaseCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_apply"
#check @MethbokeAddon.FDSNR3.physicalPhaseCorrection_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_apply"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseCorrection_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_inversePhaseCorrection"
#check @MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_inversePhaseCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_inversePhaseCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_inversePhaseCorrection"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_inversePhaseCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_inversePhaseCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_zero_parameter"
#check @MethbokeAddon.FDSNR3.physicalPhaseCorrection_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseCorrection_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_zero_of_beta_zero"
#check @MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_zero_of_beta_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_zero_of_beta_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_zero_of_beta_zero"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_zero_of_beta_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_eq_zero_of_beta_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_tsupport_subset"
#check @MethbokeAddon.FDSNR3.physicalPhaseCorrection_tsupport_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_tsupport_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_tsupport_subset"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseCorrection_tsupport_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_tsupport_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_hasCompactSupport"
#check @MethbokeAddon.FDSNR3.physicalPhaseCorrection_hasCompactSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_hasCompactSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_hasCompactSupport"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseCorrection_hasCompactSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_hasCompactSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalCorrectionSlice"
#check @MethbokeAddon.FDSNR3.physicalCorrectionSlice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalCorrectionSlice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalCorrectionSlice"
#print axioms MethbokeAddon.FDSNR3.physicalCorrectionSlice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalCorrectionSlice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalCorrectionSlice_apply"
#check @MethbokeAddon.FDSNR3.physicalCorrectionSlice_apply
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalCorrectionSlice_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalCorrectionSlice_apply"
#print axioms MethbokeAddon.FDSNR3.physicalCorrectionSlice_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalCorrectionSlice_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalCorrectionSlice_coe"
#check @MethbokeAddon.FDSNR3.physicalCorrectionSlice_coe
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalCorrectionSlice_coe"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalCorrectionSlice_coe"
#print axioms MethbokeAddon.FDSNR3.physicalCorrectionSlice_coe
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalCorrectionSlice_coe"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseCorrection"
#check @MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseCorrection"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_divergence_free"
#check @MethbokeAddon.FDSNR3.physicalPhaseCorrection_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseCorrection_divergence_free"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseCorrection_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseCorrection_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.spectralCorrectionSlice_eq_phase_difference"
#check @MethbokeAddon.FDSNR3.spectralCorrectionSlice_eq_phase_difference
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.spectralCorrectionSlice_eq_phase_difference"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.spectralCorrectionSlice_eq_phase_difference"
#print axioms MethbokeAddon.FDSNR3.spectralCorrectionSlice_eq_phase_difference
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.spectralCorrectionSlice_eq_phase_difference"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalCorrectionSlice_eq_phaseSlice_sub"
#check @MethbokeAddon.FDSNR3.physicalCorrectionSlice_eq_phaseSlice_sub
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalCorrectionSlice_eq_phaseSlice_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalCorrectionSlice_eq_phaseSlice_sub"
#print axioms MethbokeAddon.FDSNR3.physicalCorrectionSlice_eq_phaseSlice_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalCorrectionSlice_eq_phaseSlice_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_zero_parameter"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_beta_zero"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_beta_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_beta_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_beta_zero"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_beta_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_beta_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_time_notMem"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_time_notMem
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_time_notMem"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_time_notMem"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_time_notMem
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_seed_of_time_notMem"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_phaseSlice"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_phaseSlice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_phaseSlice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_phaseSlice"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_phaseSlice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_eq_phaseSlice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_exists_schwartz_slice"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_exists_schwartz_slice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_exists_schwartz_slice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_exists_schwartz_slice"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_exists_schwartz_slice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_exists_schwartz_slice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily"
#check @MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_helicalPower"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_helicalPower
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_helicalPower"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_helicalPower"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_helicalPower
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_helicalPower"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily_eq_of_cutoff_zero"
#check @MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily_eq_of_cutoff_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily_eq_of_cutoff_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily_eq_of_cutoff_zero"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily_eq_of_cutoff_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity_physicalPhaseFamily_eq_of_cutoff_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_divergence_free"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_divergence_free"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_integrable_norm_sq"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_integrable_norm_sq
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_integrable_norm_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_integrable_norm_sq"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_integrable_norm_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_integrable_norm_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_energy"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_energy
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_energy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_energy"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_energy
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_energy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_gradientSquare_integrable"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_gradientSquare_integrable
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_gradientSquare_integrable"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_gradientSquare_integrable"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_gradientSquare_integrable
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_gradientSquare_integrable"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_dissipation"
#check @MethbokeAddon.FDSNR3.physicalPhaseFamily_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalPhaseFamily_dissipation"
#print axioms MethbokeAddon.FDSNR3.physicalPhaseFamily_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalPhaseFamily_dissipation"

