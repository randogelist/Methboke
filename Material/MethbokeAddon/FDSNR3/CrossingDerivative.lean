import MethbokeAddon.FDSNR3.ForwardFourierSmooth
import MethbokeAddon.FDSNR3.ForceSeparation
import MethbokeAddon.FDSNR3.CrossingTimePhase

/-!
# The genuine inverse-Fourier time derivative at a phase crossing

Differentiation under the Lebesgue inverse transform is justified by a
common compact frequency support and continuity of the actual joint
derivative. The domination is proved on a compact time-frequency cylinder.
The resulting crossing derivative is the actual Schwartz generator used
by the physical residual separation theorem.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

theorem hasCompactSupport_of_frequency_carrier
    {K : Set Vec} (hK : IsCompact K) (f : Vec → CVec)
    (hf : ∀ ξ : Vec, ξ ∉ K → f ξ = 0) : HasCompactSupport f := by
  apply hK.of_isClosed_subset (isClosed_tsupport f)
  apply closure_minimal ?_ hK.isClosed
  intro ξ hξ
  by_contra hn
  exact hξ (hf ξ hn)

theorem hasDerivAt_spectrum_time_of_joint_smooth
    {a b t : ℝ} {g : ℝ × Vec → CVec}
    (hg : ContDiffOn ℝ ∞ g {q | q.1 ∈ Ioo a b})
    (ht : t ∈ Ioo a b) (ξ : Vec) :
    HasDerivAt (fun r : ℝ => g (r, ξ))
      (fderiv ℝ g (t, ξ) (1, 0)) t := by
  have hD : IsOpen {q : ℝ × Vec | q.1 ∈ Ioo a b} :=
    isOpen_Ioo.preimage continuous_fst
  have hgat : ContDiffAt ℝ ∞ g (t, ξ) := hg.contDiffAt (hD.mem_nhds ht)
  have hd := (hgat.differentiableAt (by norm_num)).hasFDerivAt
  exact hd.comp_hasDerivAt t ((hasDerivAt_id t).prodMk (hasDerivAt_const t ξ))

/-- Genuine differentiation under the inverse Fourier integral. No
integrability, domination, or derivative interchange is assumed: each is
derived from smoothness and the common compact frequency carrier. -/
theorem inverseFourier_hasDerivAt_of_commonCompactSupport
    {a b t : ℝ} {K : Set Vec} {g : ℝ × Vec → CVec}
    (hK : IsCompact K)
    (hg : ContDiffOn ℝ ∞ g {q | q.1 ∈ Ioo a b})
    (hsupp : ∀ r ∈ Ioo a b, ∀ ξ : Vec, ξ ∉ K → g (r, ξ) = 0)
    (ht : t ∈ Ioo a b) (x : Vec) :
    HasDerivAt (fun r : ℝ => 𝓕⁻ (fun ξ : Vec => g (r, ξ)) x)
      (𝓕⁻ (fun ξ : Vec => fderiv ℝ g (t, ξ) (1, 0)) x) t := by
  let D : Set (ℝ × Vec) := {q | q.1 ∈ Ioo a b}
  let g' : ℝ × Vec → CVec := fun q => fderiv ℝ g q (1, 0)
  have hD : IsOpen D := isOpen_Ioo.preimage continuous_fst
  have hg' : ContinuousOn g' D :=
    (hg.continuousOn_fderiv_of_isOpen hD (by norm_num)).clm_apply continuousOn_const
  have hdiff (r : ℝ) (hr : r ∈ Ioo a b) (ξ : Vec) :
      HasDerivAt (fun q : ℝ => g (q, ξ)) (g' (r, ξ)) r :=
    hasDerivAt_spectrum_time_of_joint_smooth hg hr ξ
  have hsupp' (r : ℝ) (hr : r ∈ Ioo a b) (ξ : Vec) (hξ : ξ ∉ K) :
      g' (r, ξ) = 0 := by
    have hz : (fun q : ℝ => g (q, ξ)) =ᶠ[𝓝 r] 0 :=
      (Ioo_mem_nhds hr.1 hr.2).mono (fun q hq => hsupp q hq ξ hξ)
    exact (hdiff r hr ξ).unique ((hasDerivAt_const r (0 : CVec)).congr_of_eventuallyEq hz)
  have hgc (r : ℝ) (hr : r ∈ Ioo a b) :
      Continuous (fun ξ : Vec => g (r, ξ)) :=
    hg.continuousOn.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hr)
  have hg'c (r : ℝ) (hr : r ∈ Ioo a b) :
      Continuous (fun ξ : Vec => g' (r, ξ)) :=
    hg'.comp_continuous (continuous_const.prodMk continuous_id) (fun _ => hr)
  have hInt (r : ℝ) (hr : r ∈ Ioo a b) :
      Integrable (fun ξ : Vec => g (r, ξ)) :=
    (hgc r hr).integrable_of_hasCompactSupport
      (hasCompactSupport_of_frequency_carrier hK _ (hsupp r hr))
  have hInt' (r : ℝ) (hr : r ∈ Ioo a b) :
      Integrable (fun ξ : Vec => g' (r, ξ)) :=
    (hg'c r hr).integrable_of_hasCompactSupport
      (hasCompactSupport_of_frequency_carrier hK _ (hsupp' r hr))
  have hFInt (r : ℝ) (hr : r ∈ Ioo a b) :
      Integrable (fun ξ : Vec => Real.fourierChar (inner ℝ ξ x) • g (r, ξ)) := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).mpr (hInt r hr)
  have hFInt' (r : ℝ) (hr : r ∈ Ioo a b) :
      Integrable (fun ξ : Vec => Real.fourierChar (inner ℝ ξ x) • g' (r, ξ)) := by
    simpa only [inner_neg_right, neg_neg] using
      (Real.fourierIntegral_convergent_iff (-x)).mpr (hInt' r hr)
  let l : ℝ := (a + t) / 2
  let r : ℝ := (t + b) / 2
  have hal : a < l := by dsimp [l]; linarith [ht.1]
  have hlt : l < t := by dsimp [l]; linarith [ht.1]
  have htr : t < r := by dsimp [r]; linarith [ht.2]
  have hrb : r < b := by dsimp [r]; linarith [ht.2]
  have hsub : Icc l r ×ˢ K ⊆ D := by
    intro q hq
    exact ⟨hal.trans_le hq.1.1, hq.1.2.trans_lt hrb⟩
  have hsubtime : Ioo l r ⊆ Ioo a b :=
    fun _ hq => ⟨hal.trans hq.1, hq.2.trans hrb⟩
  obtain ⟨C, hC⟩ := (isCompact_Icc.prod hK).exists_bound_of_continuousOn (hg'.mono hsub)
  let B : Vec → ℝ := K.indicator (fun _ => max 0 C)
  have hB : Integrable B :=
    (integrableOn_const hK.measure_lt_top.ne).integrable_indicator hK.measurableSet
  have hbound : ∀ᵐ ξ : Vec, ∀ q ∈ Ioo l r,
      ‖Real.fourierChar (inner ℝ ξ x) • g' (q, ξ)‖ ≤ B ξ := by
    apply ae_of_all
    intro ξ q hq
    rw [Circle.norm_smul]
    by_cases hξ : ξ ∈ K
    · change ‖g' (q, ξ)‖ ≤ K.indicator (fun _ => max 0 C) ξ
      rw [Set.indicator_of_mem hξ]
      exact (hC (q, ξ) ⟨⟨hq.1.le, hq.2.le⟩, hξ⟩).trans (le_max_right _ _)
    · rw [hsupp' q (hsubtime hq) ξ hξ, norm_zero]
      simp only [B, Set.indicator_of_notMem hξ, le_refl]
  have hFdiff : ∀ᵐ ξ : Vec, ∀ q ∈ Ioo l r,
      HasDerivAt (fun q : ℝ => Real.fourierChar (inner ℝ ξ x) • g (q, ξ))
        (Real.fourierChar (inner ℝ ξ x) • g' (q, ξ)) q := by
    apply ae_of_all
    intro ξ q hq
    change HasDerivAt (fun q : ℝ => (Real.fourierChar (inner ℝ ξ x) : ℂ) • g (q, ξ))
      ((Real.fourierChar (inner ℝ ξ x) : ℂ) • g' (q, ξ)) q
    exact (hdiff q (hsubtime hq) ξ).const_smul _
  have hd := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (Ioo_mem_nhds hlt htr)
    ((Ioo_mem_nhds hlt htr).mono (fun q hq => (hFInt q (hsubtime hq)).aestronglyMeasurable))
    (hFInt t ht) (hFInt' t ht).aestronglyMeasurable hbound hB hFdiff).2
  simpa only [Real.fourierInv_eq, g'] using hd

/-- The raw physical correction, with the actual inverse Lebesgue transform
and the seed's actual Fourier velocity. -/
def inversePhaseCorrection (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (lam : ℝ) (u : Velocity) : Velocity :=
  fun t x => realify (𝓕⁻ (fun ξ : Vec =>
    packetPhaseIncrement β ψ lam t ξ • fourierVelocity (u t) ξ) x)

theorem inversePhaseCorrection_eq_zero_of_beta_zero
    {β : ℝ → ℝ} (ψ : Vec → ℝ) (lam : ℝ) (u : Velocity)
    {t : ℝ} (hβ : β t = 0) : inversePhaseCorrection β ψ lam u t = 0 := by
  have hz : (fun ξ : Vec => packetPhaseIncrement β ψ lam t ξ •
      fourierVelocity (u t) ξ) = 0 := by
    funext ξ
    simp [packetPhaseIncrement, packetPhase_eq_one_of_beta_zero ψ lam hβ]
  funext x
  change realify (𝓕⁻ (fun ξ : Vec => packetPhaseIncrement β ψ lam t ξ •
      fourierVelocity (u t) ξ) x) = 0
  rw [hz]
  simp only [Real.fourierInv_eq, Pi.zero_apply, smul_zero, integral_zero] <;> rfl

theorem hasDerivAt_packetPhaseIncrement_at_crossing
    {β : ℝ → ℝ} (ψ : Vec → ℝ) (lam : ℝ) {t slope : ℝ}
    (hβ : HasDerivAt β slope t) (hzero : β t = 0) (ξ : Vec) :
    HasDerivAt (fun r : ℝ => packetPhaseIncrement β ψ lam r ξ)
      (((lam * slope * ψ ξ : ℝ) : ℂ) * Complex.I) t := by
  have hreal := (hβ.const_mul lam).mul_const (ψ ξ)
  have hc := (Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t hreal).mul_const Complex.I
  have he := hc.cexp.sub_const 1
  simpa [packetPhaseIncrement, packetPhase, MethbokeAddon.FDSN.phase, hzero] using he


/-- The inverse phase correction has the actual generator derivative at
the signed crossing. The seed's Fourier derivative term cancels because
the phase increment is zero at that time. -/
theorem LocalSchwartz.hasDerivAt_inversePhaseCorrection_at_crossing
    {T t slope : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} (hβsmooth : ContDiff ℝ ∞ β)
    (ψ : Vec → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ht : t ∈ Ioo (0 : ℝ) T) (hβ : HasDerivAt β slope t) (hzero : β t = 0)
    (lam : ℝ) (x : Vec) :
    HasDerivAt (fun r : ℝ => inversePhaseCorrection β ψ lam u r x)
      ((lam * slope) • spectralGenerator ψ hψ hcψ (hu.slice ⟨ht.1.le, ht.2⟩) x) t := by
  let g : ℝ × Vec → CVec := fun q =>
    packetPhaseIncrement β ψ lam q.1 q.2 • fourierVelocity (u q.1) q.2
  have hphase : ContDiff ℝ ∞
      (fun q : ℝ × Vec => packetPhaseIncrement β ψ lam q.1 q.2) :=
    (contDiff_packetPhaseIncrement_joint hβsmooth hψ).comp
      (contDiff_const.prodMk contDiff_id)
  have hg : ContDiffOn ℝ ∞ g {q | q.1 ∈ Ioo (0 : ℝ) T} :=
    hphase.contDiffOn.smul hu.contDiffOn_fourierVelocity
  have hsupp : ∀ r ∈ Ioo (0 : ℝ) T, ∀ ξ : Vec, ξ ∉ tsupport ψ → g (r, ξ) = 0 := by
    intro r _ ξ hξ
    have hψzero : ψ ξ = 0 := image_eq_zero_of_notMem_tsupport hξ
    simp only [g, packetPhaseIncrement,
      packetPhase_eq_one_of_psi_zero β lam r hψzero, sub_self, zero_smul]
  let a : 𝓢(Vec, CVec) := generatorSpectrum ψ hψ hcψ (hu.slice ⟨ht.1.le, ht.2⟩)
  have hjet (ξ : Vec) :
      fderiv ℝ g (t, ξ) (1, 0) = (lam * slope) • a ξ := by
    have hs := hasDerivAt_packetPhaseIncrement_at_crossing ψ lam hβ hzero ξ
    have hp := hs.smul (hu.hasDerivAt_fourier_time ht ξ)
    have hp' : HasDerivAt (fun r : ℝ => g (r, ξ))
        ((((lam * slope * ψ ξ : ℝ) : ℂ) * Complex.I) • fourierVelocity (u t) ξ) t := by
      simpa only [g, packetPhaseIncrement,
        packetPhase_eq_one_of_beta_zero ψ lam hzero, sub_self, zero_smul, zero_add] using hp
    rw [(hasDerivAt_spectrum_time_of_joint_smooth hg ht ξ).unique hp']
    change ((((lam * slope * ψ ξ : ℝ) : ℂ) * Complex.I) • fourierVelocity (u t) ξ) =
      (lam * slope) • ((Complex.I * (ψ ξ : ℂ)) • fourierVelocity (u t) ξ)
    rw [← smul_assoc]
    congr 1
    change ((lam * slope * ψ ξ : ℝ) : ℂ) * Complex.I =
      ((lam * slope : ℝ) : ℂ) * (Complex.I * (ψ ξ : ℂ))
    push_cast
    ring
  have hspec : (fun ξ : Vec => fderiv ℝ g (t, ξ) (1, 0)) =
      ((lam * slope) • a : 𝓢(Vec, CVec)) := funext hjet
  have hinv := inverseFourier_hasDerivAt_of_commonCompactSupport
    hcψ.isCompact hg hsupp ht x
  have hreal := realifyCLM.hasFDerivAt.comp_hasDerivAt t hinv
  have hvalue : realifyCLM (𝓕⁻ (fun ξ : Vec => fderiv ℝ g (t, ξ) (1, 0)) x) =
      (lam * slope) • spectralGenerator ψ hψ hcψ (hu.slice ⟨ht.1.le, ht.2⟩) x := by
    rw [hspec, ← SchwartzMap.fourierInv_coe, FourierTransform.fourierInv_smul]
    change realifyCLM ((lam * slope) • (𝓕⁻ a) x) =
      (lam * slope) • realifyCLM ((𝓕⁻ a) x)
    exact map_smul realifyCLM (lam * slope) ((𝓕⁻ a) x)
  rw [hvalue] at hreal
  exact hreal

/-- The preceding genuine derivative is the native right-domain derivative
used by the Navier--Stokes contract at every positive crossing time. -/
theorem LocalSchwartz.timeDerivative_inversePhaseCorrection_at_crossing
    {T t slope : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} (hβsmooth : ContDiff ℝ ∞ β)
    (ψ : Vec → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ht : t ∈ Ioo (0 : ℝ) T) (hβ : HasDerivAt β slope t) (hzero : β t = 0)
    (lam : ℝ) :
    timeDerivative (inversePhaseCorrection β ψ lam u) t =
      (lam * slope) • (spectralGenerator ψ hψ hcψ (hu.slice ⟨ht.1.le, ht.2⟩) : Field) := by
  funext x
  rw [timeDerivative, derivWithin_of_mem_nhds (Ici_mem_nhds ht.1)]
  exact (hu.hasDerivAt_inversePhaseCorrection_at_crossing
    hβsmooth ψ hψ hcψ ht hβ hzero lam x).deriv

/-- Concrete physical force separation for the actual inverse phase
family. The analytic crossing derivative is proved above, and the nonzero
generator is obtained from an actual nonzero Fourier coefficient. -/
theorem physicalProjectedForceSeparation_inversePhaseCorrection
    (ν T ε tzero slope : ℝ) (u F : Velocity)
    (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} (hβsmooth : ContDiff ℝ ∞ β)
    (ψ : Vec → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (htzero : tzero ∈ Ioo (0 : ℝ) T)
    (hβ : HasDerivAt β slope tzero) (hzero : β tzero = 0) (hslope : slope ≠ 0)
    (hdiv : ∀ x : Vec, divergence (u tzero) x = 0)
    {ξ : Vec} {i : Fin 3} (hψξ : ψ ξ ≠ 0)
    (hactive : fourierVelocity (u tzero) ξ i ≠ 0) :
    PhysicalProjectedForceSeparation T ε
      (fun lam => MethbokeAddon.FDSN.residualForce ν u F
        (inversePhaseCorrection β ψ lam u)) := by
  let f := hu.slice ⟨htzero.1.le, htzero.2⟩
  apply physicalProjectedForceSeparation_of_common_crossing ν T ε tzero slope u F
    (fun lam => inversePhaseCorrection β ψ lam u)
    (spectralGenerator ψ hψ hcψ f) ⟨htzero.1.le, htzero.2⟩ hslope
  · exact spectralGenerator_ne_zero ψ hψ hcψ ho f hψξ hactive
  · exact spectralGenerator_divergence_free ψ hψ hcψ ho f hdiv
  · intro lam _
    exact inversePhaseCorrection_eq_zero_of_beta_zero ψ lam u hzero
  · intro lam _
    exact hu.timeDerivative_inversePhaseCorrection_at_crossing
      hβsmooth ψ hψ hcψ htzero hβ hzero lam


end

end MethbokeAddon.FDSNR3

