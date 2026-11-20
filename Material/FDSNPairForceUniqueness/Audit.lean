import FDSNPairForceUniqueness.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/- Explicit full-type consumers; root supplies imports and audit sentinels. -/

noncomputable section
open Set SingularClosure MethbokeAddon.FDSN
open scoped BigOperators ContDiff

example : ∀ (c d : FourierCoeff),
    SpectralSolenoidal c → SpectralSolenoidal d → SpectralSolenoidal (c - d) :=
  @MethbokeAddon.FDSN.spectralSolenoidal_sub

example : ∀ (k : Frequency) (v w : Fin 3 → ℂ),
    coefficientLeray k (v - w) = coefficientLeray k v - coefficientLeray k w :=
  @MethbokeAddon.FDSN.coefficientLeray_sub_arg

example : ∀ (c d : TorusSobolev 0) (a : Frequency) (i : Fin 3),
    SpectralSolenoidal c.val → SpectralSolenoidal d.val →
    PairSupported a (d.val - c.val) →
    coefficientLeray a (fullTransportCoefficients d a) i -
        coefficientLeray a (fullTransportCoefficients c a) i =
      meanTransportFactor c.val a * (d.val a i - c.val a i) :=
  @MethbokeAddon.FDSN.projectedTransport_pair_difference

example : ∀ {ν T : ℝ} {u v F G : Velocity} {p q : Pressure},
    PreterminalNSE ν T u p F → PreterminalNSE ν T v q G →
    ∀ (t : ℝ), t ∈ Ioo (0 : ℝ) T →
    Continuous (F t) → Continuous (G t) → ∀ (a : Frequency) (i : Fin 3),
    PairSupported a (datumFourierCoeff (v t) - datumFourierCoeff (u t)) →
    coefficientLeray a (datumFourierCoeff (G t) a) i =
      coefficientLeray a (datumFourierCoeff (F t) a) i →
    HasDerivAt
      (fun r => datumFourierCoeff (v r) a i - datumFourierCoeff (u r) a i)
      (-(((ν * laplacianFrequency a : ℝ) : ℂ) +
          meanTransportFactor (datumFourierCoeff (u t)) a) *
        (datumFourierCoeff (v t) a i - datumFourierCoeff (u t) a i)) t :=
  @MethbokeAddon.FDSN.PreterminalNSE.pair_difference_hasDerivAt

example : ∀ {ν T : ℝ} {u v F G : Velocity} {p q : Pressure},
    PreterminalNSE ν T u p F → PreterminalNSE ν T v q G →
    0 ≤ ν → ∀ (s t : ℝ), 0 < s → s ≤ t → t < T →
    ∀ (a : Frequency) (i : Fin 3),
    (∀ r ∈ Ioo s t, Continuous (F r)) →
    (∀ r ∈ Ioo s t, Continuous (G r)) →
    (∀ r ∈ Ioo s t,
      PairSupported a (datumFourierCoeff (v r) - datumFourierCoeff (u r))) →
    (∀ r ∈ Ioo s t,
      coefficientLeray a (datumFourierCoeff (G r) a) i =
        coefficientLeray a (datumFourierCoeff (F r) a) i) →
    datumFourierCoeff (v s) a i = datumFourierCoeff (u s) a i →
    ∀ r ∈ Icc s t, datumFourierCoeff (v r) a i = datumFourierCoeff (u r) a i :=
  @MethbokeAddon.FDSN.PreterminalNSE.pair_mode_eq_on_Icc

example : ∀ {ν T : ℝ} {u v F G : Velocity} {p q : Pressure},
    PreterminalNSE ν T u p F → PreterminalNSE ν T v q G →
    0 ≤ ν → ∀ (s t : ℝ), 0 < s → s ≤ t → t < T →
    ∀ (a : Frequency) (i : Fin 3),
    (∀ r ∈ Ioo s t, Continuous (F r)) →
    (∀ r ∈ Ioo s t, Continuous (G r)) →
    (∀ r ∈ Ioo s t,
      PairSupported a (datumFourierCoeff (v r) - datumFourierCoeff (u r))) →
    datumFourierCoeff (v s) a i = datumFourierCoeff (u s) a i →
    datumFourierCoeff (v t) a i ≠ datumFourierCoeff (u t) a i →
    ∃ r ∈ Ioo s t,
      coefficientLeray a (datumFourierCoeff (G r) a) i ≠
        coefficientLeray a (datumFourierCoeff (F r) a) i :=
  @MethbokeAddon.FDSN.PreterminalNSE.projected_force_ne_of_pair_mode_ne

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.spectralSolenoidal_sub"
#check @MethbokeAddon.FDSN.spectralSolenoidal_sub
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.spectralSolenoidal_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.spectralSolenoidal_sub"
#print axioms MethbokeAddon.FDSN.spectralSolenoidal_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.spectralSolenoidal_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.coefficientLeray_sub_arg"
#check @MethbokeAddon.FDSN.coefficientLeray_sub_arg
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.coefficientLeray_sub_arg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.coefficientLeray_sub_arg"
#print axioms MethbokeAddon.FDSN.coefficientLeray_sub_arg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.coefficientLeray_sub_arg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.projectedTransport_pair_difference"
#check @MethbokeAddon.FDSN.projectedTransport_pair_difference
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.projectedTransport_pair_difference"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.projectedTransport_pair_difference"
#print axioms MethbokeAddon.FDSN.projectedTransport_pair_difference
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.projectedTransport_pair_difference"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.pair_difference_hasDerivAt"
#check @MethbokeAddon.FDSN.PreterminalNSE.pair_difference_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.pair_difference_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.pair_difference_hasDerivAt"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.pair_difference_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.pair_difference_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.pair_mode_eq_on_Icc"
#check @MethbokeAddon.FDSN.PreterminalNSE.pair_mode_eq_on_Icc
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.pair_mode_eq_on_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.pair_mode_eq_on_Icc"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.pair_mode_eq_on_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.pair_mode_eq_on_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.projected_force_ne_of_pair_mode_ne"
#check @MethbokeAddon.FDSN.PreterminalNSE.projected_force_ne_of_pair_mode_ne
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.projected_force_ne_of_pair_mode_ne"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.projected_force_ne_of_pair_mode_ne"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.projected_force_ne_of_pair_mode_ne
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.projected_force_ne_of_pair_mode_ne"

