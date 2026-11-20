import FDSNPairTransport.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/- Explicit full-type consumers; root supplies imports and audit sentinels. -/

noncomputable section
open SingularClosure
open MethbokeAddon.FDSN
open scoped BigOperators

example : (PairSupported : Frequency → FourierCoeff → Prop) =
    (fun a h => ∀ p : Frequency, p ≠ a → p ≠ -a → h p = 0) := rfl

example : (mixedTransportModeTerm : FourierCoeff → FourierCoeff → Frequency →
    Frequency → Fin 3 → ℂ) =
    (fun c d k p i => ∑ j : Fin 3, derivativeSymbol j k * c p j * d (k - p) i) := rfl

example : ∀ (c d : FourierCoeff) (k p : Frequency) (i : Fin 3),
    mixedTransportModeTerm c d k p i =
      (∑ j : Fin 3, derivativeSymbol j k * c p j) * d (k - p) i :=
  @MethbokeAddon.FDSN.mixedTransportModeTerm_factored

example : ∀ (c d : TorusSobolev 0) (k : Frequency) (i : Fin 3),
    HasSum (fun p : Frequency => mixedTransportModeTerm c.val d.val k p i)
      (divergenceTransportCoefficient k i c d) :=
  @MethbokeAddon.FDSN.divergenceTransportCoefficient_hasSum

example : ∀ (c : FourierCoeff) (hsol : SpectralSolenoidal c) (a : Frequency),
    (∑ j : Fin 3, derivativeSymbol j a * c (-a) j) = 0 :=
  @MethbokeAddon.FDSN.solenoidal_derivativeSum_at_negative

example : ∀ (c : FourierCoeff) (hsol : SpectralSolenoidal c) (a : Frequency),
    (∑ j : Fin 3, derivativeSymbol j a * c (a + a) j) = 0 :=
  @MethbokeAddon.FDSN.solenoidal_derivativeSum_at_double

example : ∀ (h c : TorusSobolev 0) (a : Frequency) (i : Fin 3)
    (hsol : SpectralSolenoidal h.val) (hsupp : PairSupported a h.val),
    divergenceTransportCoefficient a i h c = 0 :=
  @MethbokeAddon.FDSN.divergenceTransport_pair_left

example : ∀ (c h : TorusSobolev 0) (a : Frequency) (i : Fin 3)
    (hsol : SpectralSolenoidal c.val) (hsupp : PairSupported a h.val),
    divergenceTransportCoefficient a i c h =
      meanTransportFactor c.val a * h.val a i :=
  @MethbokeAddon.FDSN.divergenceTransport_pair_right

example : ∀ (c h : TorusSobolev 0) (a : Frequency) (i : Fin 3)
    (hc : SpectralSolenoidal c.val) (hh : SpectralSolenoidal h.val)
    (hsupp : PairSupported a h.val),
    fullTransportCoefficients (c + h) a i - fullTransportCoefficients c a i =
      meanTransportFactor c.val a * h.val a i :=
  @MethbokeAddon.FDSN.fullTransport_pair_difference

example : ∀ (c h : TorusSobolev 0) (a : Frequency) (i : Fin 3)
    (hreal : SpectralReality c.val) (hc : SpectralSolenoidal c.val)
    (hh : SpectralSolenoidal h.val) (hsupp : PairSupported a h.val),
    (star (h.val a i) *
      (fullTransportCoefficients (c + h) a i - fullTransportCoefficients c a i)).re = 0 :=
  @MethbokeAddon.FDSN.fullTransport_pair_difference_real_transfer_zero

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PairSupported"
#check @MethbokeAddon.FDSN.PairSupported
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PairSupported"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PairSupported"
#print axioms MethbokeAddon.FDSN.PairSupported
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PairSupported"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.mixedTransportModeTerm"
#check @MethbokeAddon.FDSN.mixedTransportModeTerm
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.mixedTransportModeTerm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.mixedTransportModeTerm"
#print axioms MethbokeAddon.FDSN.mixedTransportModeTerm
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.mixedTransportModeTerm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.mixedTransportModeTerm_factored"
#check @MethbokeAddon.FDSN.mixedTransportModeTerm_factored
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.mixedTransportModeTerm_factored"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.mixedTransportModeTerm_factored"
#print axioms MethbokeAddon.FDSN.mixedTransportModeTerm_factored
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.mixedTransportModeTerm_factored"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.divergenceTransportCoefficient_hasSum"
#check @MethbokeAddon.FDSN.divergenceTransportCoefficient_hasSum
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.divergenceTransportCoefficient_hasSum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.divergenceTransportCoefficient_hasSum"
#print axioms MethbokeAddon.FDSN.divergenceTransportCoefficient_hasSum
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.divergenceTransportCoefficient_hasSum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.solenoidal_derivativeSum_at_negative"
#check @MethbokeAddon.FDSN.solenoidal_derivativeSum_at_negative
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.solenoidal_derivativeSum_at_negative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.solenoidal_derivativeSum_at_negative"
#print axioms MethbokeAddon.FDSN.solenoidal_derivativeSum_at_negative
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.solenoidal_derivativeSum_at_negative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.solenoidal_derivativeSum_at_double"
#check @MethbokeAddon.FDSN.solenoidal_derivativeSum_at_double
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.solenoidal_derivativeSum_at_double"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.solenoidal_derivativeSum_at_double"
#print axioms MethbokeAddon.FDSN.solenoidal_derivativeSum_at_double
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.solenoidal_derivativeSum_at_double"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.divergenceTransport_pair_left"
#check @MethbokeAddon.FDSN.divergenceTransport_pair_left
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.divergenceTransport_pair_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.divergenceTransport_pair_left"
#print axioms MethbokeAddon.FDSN.divergenceTransport_pair_left
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.divergenceTransport_pair_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.divergenceTransport_pair_right"
#check @MethbokeAddon.FDSN.divergenceTransport_pair_right
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.divergenceTransport_pair_right"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.divergenceTransport_pair_right"
#print axioms MethbokeAddon.FDSN.divergenceTransport_pair_right
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.divergenceTransport_pair_right"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.fullTransport_pair_difference"
#check @MethbokeAddon.FDSN.fullTransport_pair_difference
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.fullTransport_pair_difference"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.fullTransport_pair_difference"
#print axioms MethbokeAddon.FDSN.fullTransport_pair_difference
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.fullTransport_pair_difference"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.fullTransport_pair_difference_real_transfer_zero"
#check @MethbokeAddon.FDSN.fullTransport_pair_difference_real_transfer_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.fullTransport_pair_difference_real_transfer_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.fullTransport_pair_difference_real_transfer_zero"
#print axioms MethbokeAddon.FDSN.fullTransport_pair_difference_real_transfer_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.fullTransport_pair_difference_real_transfer_zero"

