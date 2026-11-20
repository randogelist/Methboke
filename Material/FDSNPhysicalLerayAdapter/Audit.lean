import FDSNPhysicalLerayAdapter.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false

noncomputable section

open Set SingularClosure
open MethbokeAddon.FeffermanFamily MethbokeAddon.FDSN
open scoped ContDiff

example (v : Field) : physicalLerayProjection v =
    smoothFourierSynthesis (fun k => coefficientLeray k (datumFourierCoeff v k)) := rfl

example {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (i : Fin 3) :
    RapidScalarFourier (fun k => coefficientLeray k (datumFourierCoeff v k) i) :=
  physicalLerayProjection_rapid hv hp i

example {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    ContDiff ℝ ∞ (physicalLerayProjection v) :=
  physicalLerayProjection_smooth hv hp

example (v : Field) :
    SpatialPeriodic (physicalLerayProjection v) :=
  physicalLerayProjection_periodic v

example {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    datumFourierCoeff (physicalLerayProjection v) =
      fun k => coefficientLeray k (datumFourierCoeff v k) :=
  physicalLerayProjection_coeff hv hp

example {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    datumFourierCoeff (physicalLerayProjection v) 0 = datumFourierCoeff v 0 :=
  physicalLerayProjection_zero_mode hv hp

example {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    physicalLerayProjection v =
      v + SingularClosure.gradient (infiniteTransportPressure (datumFourierCoeff v)) :=
  physicalLerayProjection_helmholtz hv hp

example {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (x : Vec) :
    divergence (physicalLerayProjection v) x = 0 :=
  physicalLerayProjection_divergence_free hv hp x

example (v w : Field)
    (hv : Continuous v) (hw : Continuous w) :
    datumFourierCoeff (v - w) = datumFourierCoeff v - datumFourierCoeff w :=
  datumFourierCoeff_sub_continuous v w hv hw

example
    {v : Field} (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v)
    {k : Frequency} {i : Fin 3}
    (hne : coefficientLeray k (datumFourierCoeff v k) i ≠ 0) :
    physicalLerayProjection v ≠ 0 :=
  physicalLerayProjection_ne_zero_of_coefficient_ne_zero hv hp hne

example
    {T ε : ℝ} {G : ℝ → Velocity}
    (hG : ∀ lambda : ℝ, |lambda| < ε → AdmissiblePeriodicForce (G lambda))
    (hsep : ∀ lambda eta : ℝ, |lambda| < ε → |eta| < ε → lambda ≠ eta →
      ∃ t ∈ Ico (0 : ℝ) T, ∃ k : Frequency, ∃ i : Fin 3,
        coefficientLeray k (datumFourierCoeff (G lambda t) k) i ≠
          coefficientLeray k (datumFourierCoeff (G eta t) k) i) :
    ∀ lambda eta : ℝ, |lambda| < ε → |eta| < ε → lambda ≠ eta →
      ∃ t ∈ Ico (0 : ℝ) T, ∃ x : Vec,
        physicalLerayProjection ((G lambda - G eta) t) x ≠ 0 :=
  projectedForceSeparation_physical hG hsep


#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection"
#check @MethbokeAddon.FDSN.physicalLerayProjection
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalLerayProjection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection"
#print axioms MethbokeAddon.FDSN.physicalLerayProjection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalLerayProjection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_rapid"
#check @MethbokeAddon.FDSN.physicalLerayProjection_rapid
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalLerayProjection_rapid"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_rapid"
#print axioms MethbokeAddon.FDSN.physicalLerayProjection_rapid
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalLerayProjection_rapid"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_smooth"
#check @MethbokeAddon.FDSN.physicalLerayProjection_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalLerayProjection_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_smooth"
#print axioms MethbokeAddon.FDSN.physicalLerayProjection_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalLerayProjection_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_periodic"
#check @MethbokeAddon.FDSN.physicalLerayProjection_periodic
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalLerayProjection_periodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_periodic"
#print axioms MethbokeAddon.FDSN.physicalLerayProjection_periodic
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalLerayProjection_periodic"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_coeff"
#check @MethbokeAddon.FDSN.physicalLerayProjection_coeff
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalLerayProjection_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_coeff"
#print axioms MethbokeAddon.FDSN.physicalLerayProjection_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalLerayProjection_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_zero_mode"
#check @MethbokeAddon.FDSN.physicalLerayProjection_zero_mode
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalLerayProjection_zero_mode"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_zero_mode"
#print axioms MethbokeAddon.FDSN.physicalLerayProjection_zero_mode
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalLerayProjection_zero_mode"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_helmholtz"
#check @MethbokeAddon.FDSN.physicalLerayProjection_helmholtz
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalLerayProjection_helmholtz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_helmholtz"
#print axioms MethbokeAddon.FDSN.physicalLerayProjection_helmholtz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalLerayProjection_helmholtz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_divergence_free"
#check @MethbokeAddon.FDSN.physicalLerayProjection_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalLerayProjection_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_divergence_free"
#print axioms MethbokeAddon.FDSN.physicalLerayProjection_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalLerayProjection_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.datumFourierCoeff_sub_continuous"
#check @MethbokeAddon.FDSN.datumFourierCoeff_sub_continuous
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.datumFourierCoeff_sub_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.datumFourierCoeff_sub_continuous"
#print axioms MethbokeAddon.FDSN.datumFourierCoeff_sub_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.datumFourierCoeff_sub_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_ne_zero_of_coefficient_ne_zero"
#check @MethbokeAddon.FDSN.physicalLerayProjection_ne_zero_of_coefficient_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.physicalLerayProjection_ne_zero_of_coefficient_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.physicalLerayProjection_ne_zero_of_coefficient_ne_zero"
#print axioms MethbokeAddon.FDSN.physicalLerayProjection_ne_zero_of_coefficient_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.physicalLerayProjection_ne_zero_of_coefficient_ne_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.projectedForceSeparation_physical"
#check @MethbokeAddon.FDSN.projectedForceSeparation_physical
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.projectedForceSeparation_physical"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.projectedForceSeparation_physical"
#print axioms MethbokeAddon.FDSN.projectedForceSeparation_physical
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.projectedForceSeparation_physical"

