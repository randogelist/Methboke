import EhrenfestErrorEquation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independent exact consumer types; external evidence pending. -/


section Consumer1
open Set MeasureTheory SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff RealInnerProductSpace
open MethbokeAddon.EhrenfestObstruction

example (a b : Field) (ha : Continuous a) (hb : Continuous b) :
    datumFourierCoeff (a - b) = datumFourierCoeff a - datumFourierCoeff b :=
  MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_sub a b ha hb

example (k : Frequency) (v w : Fin 3 → ℂ) :
    coefficientLeray k (v - w) = coefficientLeray k v - coefficientLeray k w :=
  MethbokeAddon.EhrenfestObstruction.coefficientLeray_sub_arg k v w

example (N : ℕ) (U : Field) (c b w : FourierCoeff)
    (hU : ContDiff ℝ ∞ U) (hsum : c = w + b) :
    finiteReferenceErrorForcing N U b w =
      convection U - convection (finiteSynthesis N c) + convection (finiteSynthesis N w) :=
  finiteReferenceErrorForcing_eq_convection N U c b w hU hsum

example (N : ℕ) (U : Field) (c b w : FourierCoeff)
    (hU : ContDiff ℝ ∞ U) (hsum : c = w + b)
    (hcsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hcreal : SpectralReality c)
    (hwsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, w k i = 0)
    (hwreal : SpectralReality w) :
    datumFourierCoeff (finiteReferenceErrorForcing N U b w) =
      datumFourierCoeff (convection U) - coefficientTransport N c + coefficientTransport N w :=
  finiteReferenceErrorForcing_fourier N U c b w hU hsum hcsupp hcreal hwsupp hwreal

example (ν : ℝ) (N : ℕ) (U : Field) (c b w : FourierCoeff)
    (hU : ContDiff ℝ ∞ U) (hsum : c = w + b)
    (hcsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hcreal : SpectralReality c)
    (hwsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, w k i = 0)
    (hwreal : SpectralReality w)
    (k : Frequency) (hk : k ∈ cutoffModes N) (i : Fin 3) :
    galerkinRhs ν N c k i -
        (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * b k i -
          coefficientLeray k (datumFourierCoeff (convection U) k) i) =
      galerkinRhs ν N w k i +
        cutoffCoeff N (fun l => coefficientLeray l
          (datumFourierCoeff (finiteReferenceErrorForcing N U b w) l)) k i :=
  finite_error_rhs_identity ν N U c b w hU hsum hcsupp hcreal hwsupp hwreal k hk i

example (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (N : ℕ) (g : GalerkinSolution ν a N)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) S)
    (k : Frequency) (hk : k ∈ cutoffModes N) (i : Fin 3) :
    HasDerivAt
      (fun r => (g.coeff r - cutoffCoeff N (datumFourierCoeff (u r))) k i)
      (galerkinRhs ν N (g.coeff t - cutoffCoeff N (datumFourierCoeff (u t))) k i +
        cutoffCoeff N (fun l => coefficientLeray l
          (datumFourierCoeff (finiteReferenceErrorForcing N (u t)
            (cutoffCoeff N (datumFourierCoeff (u t)))
            (g.coeff t - cutoffCoeff N (datumFourierCoeff (u t)))) l)) k i) t :=
  initial_front_galerkin_error_hasDerivAt ν S a u p H N g t ht k hk i
end Consumer1


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_sub"
#check @MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_sub
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_sub"
#print axioms MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.datumFourierCoeff_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientLeray_sub_arg"
#check @MethbokeAddon.EhrenfestObstruction.coefficientLeray_sub_arg
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.coefficientLeray_sub_arg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientLeray_sub_arg"
#print axioms MethbokeAddon.EhrenfestObstruction.coefficientLeray_sub_arg
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.coefficientLeray_sub_arg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_eq_convection"
#check @MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_eq_convection
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_eq_convection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_eq_convection"
#print axioms MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_eq_convection
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_eq_convection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_fourier"
#check @MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_fourier
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_fourier"
#print axioms MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finiteReferenceErrorForcing_fourier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finite_error_rhs_identity"
#check @MethbokeAddon.EhrenfestObstruction.finite_error_rhs_identity
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finite_error_rhs_identity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finite_error_rhs_identity"
#print axioms MethbokeAddon.EhrenfestObstruction.finite_error_rhs_identity
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finite_error_rhs_identity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_galerkin_error_hasDerivAt"
#check @MethbokeAddon.EhrenfestObstruction.initial_front_galerkin_error_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.initial_front_galerkin_error_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.initial_front_galerkin_error_hasDerivAt"
#print axioms MethbokeAddon.EhrenfestObstruction.initial_front_galerkin_error_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.initial_front_galerkin_error_hasDerivAt"
