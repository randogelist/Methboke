import FDSNLocalizedResidual.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false

noncomputable section

open Set SingularClosure
open MethbokeAddon.WeakFouriermanB MethbokeAddon.FeffermanFamily
open MethbokeAddon.EhrenfestObstruction MethbokeAddon.FDSN
open scoped ContDiff Topology

example (ν : ℝ) (a : Frequency) (β : ℝ → ℝ)
    (u F : Velocity) (lambda : ℝ) :
    localizedPairForce ν a β u F lambda = fun t x =>
      F t x + timeDerivative (localizedPairCorrection a β u lambda) t x
        - ν • laplacian (localizedPairCorrection a β u lambda t) x
        + physicalTransport (u t) (localizedPairCorrection a β u lambda t) x
        + physicalTransport (localizedPairCorrection a β u lambda t) (u t) x
        + convection (localizedPairCorrection a β u lambda t) x := rfl

example
    (a : Frequency) (β : ℝ → ℝ) (u : Velocity) (lambda : ℝ) :
    localizedPairVelocity a β u lambda - u = localizedPairCorrection a β u lambda :=
  localizedPairVelocity_sub_eq_correction a β u lambda

example
    (ν : ℝ) (a : Frequency) (β : ℝ → ℝ) (u F : Velocity) :
    localizedPairForce ν a β u F 0 = F :=
  localizedPairForce_zero_parameter ν a β u F

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      localizedPairForce ν a β u F q.1 q.2.1 q.2.2) :=
  localizedPairForce_joint_smooth h a hβ hβs

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβs : tsupport β ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      (localizedPairForce ν a β u F q.1 - F) q.2.1 q.2.2) :=
  localizedPairForceCorrection_joint_smooth h a hβ hβs

example
    (ν : ℝ) (a : Frequency) (β : ℝ → ℝ) (u F : Velocity) (lambda : ℝ) :
    tsupport (localizedPairForce ν a β u F lambda - F) ⊆ tsupport β :=
  localizedPairForceCorrection_tsupport_subset ν a β u F lambda

example
    (ν : ℝ) (a : Frequency) {β : ℝ → ℝ} (hβ : HasCompactSupport β)
    (u F : Velocity) (lambda : ℝ) :
    HasCompactSupport (localizedPairForce ν a β u F lambda - F) :=
  localizedPairForceCorrection_hasCompactSupport ν a hβ u F lambda

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (lambda : ℝ) :
    AdmissiblePeriodicForce (localizedPairForce ν a β u F lambda) :=
  localizedPairForce_admissible h a hβ hβc hβs lambda

example
    {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F)
    (a : Frequency) {β : ℝ → ℝ} (hβ : ContDiff ℝ ∞ β)
    (hβc : HasCompactSupport β) (hβs : tsupport β ⊆ Ioo (0 : ℝ) T)
    (lambda t : ℝ) :
    SpatialPeriodic ((localizedPairForce ν a β u F lambda - F) t) :=
  localizedPairForceCorrection_periodic h a hβ hβc hβs lambda t


#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForce"
#check @MethbokeAddon.FDSN.localizedPairForce
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForce"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForce"
#print axioms MethbokeAddon.FDSN.localizedPairForce
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForce"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_sub_eq_correction"
#check @MethbokeAddon.FDSN.localizedPairVelocity_sub_eq_correction
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairVelocity_sub_eq_correction"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairVelocity_sub_eq_correction"
#print axioms MethbokeAddon.FDSN.localizedPairVelocity_sub_eq_correction
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairVelocity_sub_eq_correction"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForce_zero_parameter"
#check @MethbokeAddon.FDSN.localizedPairForce_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForce_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForce_zero_parameter"
#print axioms MethbokeAddon.FDSN.localizedPairForce_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForce_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForce_joint_smooth"
#check @MethbokeAddon.FDSN.localizedPairForce_joint_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForce_joint_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForce_joint_smooth"
#print axioms MethbokeAddon.FDSN.localizedPairForce_joint_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForce_joint_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForceCorrection_joint_smooth"
#check @MethbokeAddon.FDSN.localizedPairForceCorrection_joint_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForceCorrection_joint_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForceCorrection_joint_smooth"
#print axioms MethbokeAddon.FDSN.localizedPairForceCorrection_joint_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForceCorrection_joint_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForceCorrection_tsupport_subset"
#check @MethbokeAddon.FDSN.localizedPairForceCorrection_tsupport_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForceCorrection_tsupport_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForceCorrection_tsupport_subset"
#print axioms MethbokeAddon.FDSN.localizedPairForceCorrection_tsupport_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForceCorrection_tsupport_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForceCorrection_hasCompactSupport"
#check @MethbokeAddon.FDSN.localizedPairForceCorrection_hasCompactSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForceCorrection_hasCompactSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForceCorrection_hasCompactSupport"
#print axioms MethbokeAddon.FDSN.localizedPairForceCorrection_hasCompactSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForceCorrection_hasCompactSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForce_admissible"
#check @MethbokeAddon.FDSN.localizedPairForce_admissible
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForce_admissible"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForce_admissible"
#print axioms MethbokeAddon.FDSN.localizedPairForce_admissible
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForce_admissible"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.localizedPairForceCorrection_periodic"
#check @MethbokeAddon.FDSN.localizedPairForceCorrection_periodic
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.localizedPairForceCorrection_periodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.localizedPairForceCorrection_periodic"
#print axioms MethbokeAddon.FDSN.localizedPairForceCorrection_periodic
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.localizedPairForceCorrection_periodic"

