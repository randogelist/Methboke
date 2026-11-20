import FDSNR3CrossingDerivative.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology

example (β : ℝ → ℝ) (ψ : Vec → ℝ) (lam : ℝ) (u : Velocity) (t : ℝ) (x : Vec) :
    inversePhaseCorrection β ψ lam u t x = realify (𝓕⁻ (fun ξ : Vec =>
      packetPhaseIncrement β ψ lam t ξ • fourierVelocity (u t) ξ) x) := rfl

example : ∀ {K : Set Vec} (hK : IsCompact K) (f : Vec → CVec)
    (hf : ∀ ξ : Vec, ξ ∉ K → f ξ = 0),
    HasCompactSupport f :=
  @hasCompactSupport_of_frequency_carrier

example : ∀ {a b t : ℝ} {g : ℝ × Vec → CVec}
    (hg : ContDiffOn ℝ ∞ g {q | q.1 ∈ Ioo a b})
    (ht : t ∈ Ioo a b) (ξ : Vec),
    HasDerivAt (fun r : ℝ => g (r, ξ))
      (fderiv ℝ g (t, ξ) (1, 0)) t :=
  @hasDerivAt_spectrum_time_of_joint_smooth

example : ∀ {a b t : ℝ} {K : Set Vec} {g : ℝ × Vec → CVec}
    (hK : IsCompact K)
    (hg : ContDiffOn ℝ ∞ g {q | q.1 ∈ Ioo a b})
    (hsupp : ∀ r ∈ Ioo a b, ∀ ξ : Vec, ξ ∉ K → g (r, ξ) = 0)
    (ht : t ∈ Ioo a b) (x : Vec),
    HasDerivAt (fun r : ℝ => 𝓕⁻ (fun ξ : Vec => g (r, ξ)) x)
      (𝓕⁻ (fun ξ : Vec => fderiv ℝ g (t, ξ) (1, 0)) x) t :=
  @inverseFourier_hasDerivAt_of_commonCompactSupport

example : ∀ {β : ℝ → ℝ} (ψ : Vec → ℝ) (lam : ℝ) (u : Velocity)
    {t : ℝ} (hβ : β t = 0),
    inversePhaseCorrection β ψ lam u t = 0 :=
  @inversePhaseCorrection_eq_zero_of_beta_zero

example : ∀ {β : ℝ → ℝ} (ψ : Vec → ℝ) (lam : ℝ) {t slope : ℝ}
    (hβ : HasDerivAt β slope t) (hzero : β t = 0) (ξ : Vec),
    HasDerivAt (fun r : ℝ => packetPhaseIncrement β ψ lam r ξ)
      (((lam * slope * ψ ξ : ℝ) : ℂ) * Complex.I) t :=
  @hasDerivAt_packetPhaseIncrement_at_crossing

example : ∀ {T t slope : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} (hβsmooth : ContDiff ℝ ∞ β)
    (ψ : Vec → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ht : t ∈ Ioo (0 : ℝ) T) (hβ : HasDerivAt β slope t) (hzero : β t = 0)
    (lam : ℝ) (x : Vec),
    HasDerivAt (fun r : ℝ => inversePhaseCorrection β ψ lam u r x)
      ((lam * slope) • spectralGenerator ψ hψ hcψ (hu.slice ⟨ht.1.le, ht.2⟩) x) t :=
  @LocalSchwartz.hasDerivAt_inversePhaseCorrection_at_crossing

example : ∀ {T t slope : ℝ} {u : Velocity} (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} (hβsmooth : ContDiff ℝ ∞ β)
    (ψ : Vec → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ht : t ∈ Ioo (0 : ℝ) T) (hβ : HasDerivAt β slope t) (hzero : β t = 0)
    (lam : ℝ),
    timeDerivative (inversePhaseCorrection β ψ lam u) t =
      (lam * slope) • (spectralGenerator ψ hψ hcψ (hu.slice ⟨ht.1.le, ht.2⟩) : Field) :=
  @LocalSchwartz.timeDerivative_inversePhaseCorrection_at_crossing

example : ∀ (ν T ε tzero slope : ℝ) (u F : Velocity)
    (hu : LocalSchwartz T u)
    {β : ℝ → ℝ} (hβsmooth : ContDiff ℝ ∞ β)
    (ψ : Vec → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (htzero : tzero ∈ Ioo (0 : ℝ) T)
    (hβ : HasDerivAt β slope tzero) (hzero : β tzero = 0) (hslope : slope ≠ 0)
    (hdiv : ∀ x : Vec, divergence (u tzero) x = 0)
    {ξ : Vec} {i : Fin 3} (hψξ : ψ ξ ≠ 0)
    (hactive : fourierVelocity (u tzero) ξ i ≠ 0),
    PhysicalProjectedForceSeparation T ε
      (fun lam => MethbokeAddon.FDSN.residualForce ν u F
        (inversePhaseCorrection β ψ lam u)) :=
  @physicalProjectedForceSeparation_inversePhaseCorrection

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.hasCompactSupport_of_frequency_carrier"
#check @MethbokeAddon.FDSNR3.hasCompactSupport_of_frequency_carrier
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.hasCompactSupport_of_frequency_carrier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.hasCompactSupport_of_frequency_carrier"
#print axioms MethbokeAddon.FDSNR3.hasCompactSupport_of_frequency_carrier
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.hasCompactSupport_of_frequency_carrier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.hasDerivAt_spectrum_time_of_joint_smooth"
#check @MethbokeAddon.FDSNR3.hasDerivAt_spectrum_time_of_joint_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.hasDerivAt_spectrum_time_of_joint_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.hasDerivAt_spectrum_time_of_joint_smooth"
#print axioms MethbokeAddon.FDSNR3.hasDerivAt_spectrum_time_of_joint_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.hasDerivAt_spectrum_time_of_joint_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.inverseFourier_hasDerivAt_of_commonCompactSupport"
#check @MethbokeAddon.FDSNR3.inverseFourier_hasDerivAt_of_commonCompactSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.inverseFourier_hasDerivAt_of_commonCompactSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.inverseFourier_hasDerivAt_of_commonCompactSupport"
#print axioms MethbokeAddon.FDSNR3.inverseFourier_hasDerivAt_of_commonCompactSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.inverseFourier_hasDerivAt_of_commonCompactSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.inversePhaseCorrection"
#check @MethbokeAddon.FDSNR3.inversePhaseCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.inversePhaseCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.inversePhaseCorrection"
#print axioms MethbokeAddon.FDSNR3.inversePhaseCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.inversePhaseCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.inversePhaseCorrection_eq_zero_of_beta_zero"
#check @MethbokeAddon.FDSNR3.inversePhaseCorrection_eq_zero_of_beta_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.inversePhaseCorrection_eq_zero_of_beta_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.inversePhaseCorrection_eq_zero_of_beta_zero"
#print axioms MethbokeAddon.FDSNR3.inversePhaseCorrection_eq_zero_of_beta_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.inversePhaseCorrection_eq_zero_of_beta_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.hasDerivAt_packetPhaseIncrement_at_crossing"
#check @MethbokeAddon.FDSNR3.hasDerivAt_packetPhaseIncrement_at_crossing
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.hasDerivAt_packetPhaseIncrement_at_crossing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.hasDerivAt_packetPhaseIncrement_at_crossing"
#print axioms MethbokeAddon.FDSNR3.hasDerivAt_packetPhaseIncrement_at_crossing
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.hasDerivAt_packetPhaseIncrement_at_crossing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_inversePhaseCorrection_at_crossing"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_inversePhaseCorrection_at_crossing
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_inversePhaseCorrection_at_crossing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_inversePhaseCorrection_at_crossing"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_inversePhaseCorrection_at_crossing
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.hasDerivAt_inversePhaseCorrection_at_crossing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_inversePhaseCorrection_at_crossing"
#check @MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_inversePhaseCorrection_at_crossing
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_inversePhaseCorrection_at_crossing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_inversePhaseCorrection_at_crossing"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_inversePhaseCorrection_at_crossing
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz.timeDerivative_inversePhaseCorrection_at_crossing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_inversePhaseCorrection"
#check @MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_inversePhaseCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_inversePhaseCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_inversePhaseCorrection"
#print axioms MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_inversePhaseCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_inversePhaseCorrection"

