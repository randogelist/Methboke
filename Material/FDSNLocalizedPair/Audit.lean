import FDSNLocalizedPair.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set SingularClosure MethbokeAddon.FDSN
open scoped ContDiff Topology

noncomputable section

/- Exact consumer statements mirror the intended full signatures. -/

example (a : Frequency) (β : ℝ → ℝ) (u : Velocity)
    (lambda : ℝ) : Velocity :=
  localizedPairCorrection a β u lambda

example (a : Frequency) (β : ℝ → ℝ) (u : Velocity)
    (lambda : ℝ) : Velocity :=
  localizedPairVelocity a β u lambda

example {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (u t) :=
  Seed.velocity_slice_smooth h t ht

example {ν T : ℝ} {u F : Velocity}
    {p : Pressure} (h : Seed ν T u p F) (a : Frequency)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      localizedPairCorrection a β u q.1 q.2.1 q.2.2) :=
  localizedPairCorrection_joint_smooth h a hβ hβs

example {ν T : ℝ} {u F : Velocity}
    {p : Pressure} (h : Seed ν T u p F) (a : Frequency)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) (lambda : ℝ) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec => localizedPairCorrection a β u lambda z.1 z.2) :=
  localizedPairCorrection_smooth h a hβ hβs lambda

example (a : Frequency)
    (β : ℝ → ℝ) (u : Velocity) : localizedPairCorrection a β u 0 = 0 :=
  localizedPairCorrection_zero_parameter a β u

example (a : Frequency)
    {β : ℝ → ℝ} (u : Velocity) (lambda : ℝ) {t : ℝ}
    (ht : t ∉ tsupport β) : localizedPairCorrection a β u lambda t = 0 :=
  localizedPairCorrection_eq_zero_off_support a u lambda ht

example (a : Frequency)
    (β : ℝ → ℝ) (u : Velocity) (lambda : ℝ) :
    tsupport (localizedPairCorrection a β u lambda) ⊆ tsupport β :=
  localizedPairCorrection_tsupport_subset a β u lambda

example (a : Frequency)
    {β : ℝ → ℝ} (hβ : HasCompactSupport β) (u : Velocity) (lambda : ℝ) :
    HasCompactSupport (localizedPairCorrection a β u lambda) :=
  localizedPairCorrection_hasCompactSupport a hβ u lambda

example (a : Frequency)
    (β : ℝ → ℝ) (u : Velocity) (lambda t : ℝ) :
    SpatialPeriodic (localizedPairCorrection a β u lambda t) :=
  localizedPairCorrection_periodic a β u lambda t

example (a : Frequency)
    (β : ℝ → ℝ) (u : Velocity) : localizedPairVelocity a β u 0 = u :=
  localizedPairVelocity_zero_parameter a β u

example (a : Frequency)
    {β : ℝ → ℝ} (u : Velocity) (lambda : ℝ) {t : ℝ}
    (ht : t ∉ tsupport β) : localizedPairVelocity a β u lambda t = u t :=
  localizedPairVelocity_eq_seed_off_support a u lambda ht

example {T : ℝ} (a : Frequency)
    {β : ℝ → ℝ} (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (u : Velocity) (lambda : ℝ) : localizedPairVelocity a β u lambda 0 = u 0 :=
  localizedPairVelocity_initial a hβs u lambda

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) :
    localizedPairVelocity a β u lambda t =
      physicalPairRotation a (timePhase β lambda t) (u t) :=
  localizedPairVelocity_eq_physicalPairRotation h ha β lambda t ht

example {ν T : ℝ} {u F : Velocity}
    {p : Pressure} (h : Seed ν T u p F) (a : Frequency)
    {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      localizedPairVelocity a β u q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ico (0 : ℝ) T} :=
  localizedPairVelocity_joint_smooth h a hβ hβs

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    {a : Frequency} (ha : a ≠ 0) (β : ℝ → ℝ) (lambda t : ℝ)
    (ht : t ∈ Ico (0 : ℝ) T) :
    ContDiff ℝ ∞ (localizedPairVelocity a β u lambda t) ∧
    SpatialPeriodic (localizedPairVelocity a β u lambda t) ∧
    (∀ x : Vec, divergence (localizedPairVelocity a β u lambda t) x = 0) ∧
    spatialMean (localizedPairVelocity a β u lambda t) = spatialMean (u t) ∧
    (∀ k : Frequency, ∀ L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ,
      ‖L (datumFourierCoeff (localizedPairVelocity a β u lambda t) k)‖ =
        ‖L (datumFourierCoeff (u t) k)‖) :=
  LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA h ha β lambda t ht

example (a : Frequency) (β : ℝ → ℝ) (u : Velocity) (lambda t : ℝ) :
    localizedPairCorrection a β u lambda t =
      physicalPairCorrection a (timePhase β lambda t) (u t) := rfl
example (a : Frequency) (β : ℝ → ℝ) (u : Velocity) (lambda : ℝ) :
    localizedPairVelocity a β u lambda = u + localizedPairCorrection a β u lambda := rfl

















end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection"
#check @MethbokeAddon.FDSN.localizedPairCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection"
#print axioms MethbokeAddon.FDSN.localizedPairCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity"
#check @MethbokeAddon.FDSN.localizedPairVelocity
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed.velocity_slice_smooth"
#check @MethbokeAddon.FDSN.Seed.velocity_slice_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed.velocity_slice_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed.velocity_slice_smooth"
#print axioms MethbokeAddon.FDSN.Seed.velocity_slice_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed.velocity_slice_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_joint_smooth"
#check @MethbokeAddon.FDSN.localizedPairCorrection_joint_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairCorrection_joint_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_joint_smooth"
#print axioms MethbokeAddon.FDSN.localizedPairCorrection_joint_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairCorrection_joint_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_smooth"
#check @MethbokeAddon.FDSN.localizedPairCorrection_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairCorrection_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_smooth"
#print axioms MethbokeAddon.FDSN.localizedPairCorrection_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairCorrection_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_zero_parameter"
#check @MethbokeAddon.FDSN.localizedPairCorrection_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairCorrection_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_zero_parameter"
#print axioms MethbokeAddon.FDSN.localizedPairCorrection_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairCorrection_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_eq_zero_off_support"
#check @MethbokeAddon.FDSN.localizedPairCorrection_eq_zero_off_support
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairCorrection_eq_zero_off_support"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_eq_zero_off_support"
#print axioms MethbokeAddon.FDSN.localizedPairCorrection_eq_zero_off_support
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairCorrection_eq_zero_off_support"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_tsupport_subset"
#check @MethbokeAddon.FDSN.localizedPairCorrection_tsupport_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairCorrection_tsupport_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_tsupport_subset"
#print axioms MethbokeAddon.FDSN.localizedPairCorrection_tsupport_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairCorrection_tsupport_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_hasCompactSupport"
#check @MethbokeAddon.FDSN.localizedPairCorrection_hasCompactSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairCorrection_hasCompactSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_hasCompactSupport"
#print axioms MethbokeAddon.FDSN.localizedPairCorrection_hasCompactSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairCorrection_hasCompactSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_periodic"
#check @MethbokeAddon.FDSN.localizedPairCorrection_periodic
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairCorrection_periodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairCorrection_periodic"
#print axioms MethbokeAddon.FDSN.localizedPairCorrection_periodic
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairCorrection_periodic"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_zero_parameter"
#check @MethbokeAddon.FDSN.localizedPairVelocity_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_zero_parameter"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_eq_seed_off_support"
#check @MethbokeAddon.FDSN.localizedPairVelocity_eq_seed_off_support
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_eq_seed_off_support"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_eq_seed_off_support"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_eq_seed_off_support
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_eq_seed_off_support"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_initial"
#check @MethbokeAddon.FDSN.localizedPairVelocity_initial
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_initial"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_initial"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_initial
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_initial"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_eq_physicalPairRotation"
#check @MethbokeAddon.FDSN.localizedPairVelocity_eq_physicalPairRotation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_eq_physicalPairRotation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_eq_physicalPairRotation"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_eq_physicalPairRotation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_eq_physicalPairRotation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_joint_smooth"
#check @MethbokeAddon.FDSN.localizedPairVelocity_joint_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_joint_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_joint_smooth"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_joint_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_joint_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA"
#check @MethbokeAddon.FDSN.LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA"
#print axioms MethbokeAddon.FDSN.LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.LOCALIZED_PAIR_VELOCITY_PRESERVES_SPECTRAL_DATA"

