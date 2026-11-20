import FDSNTriadCancellation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/- Explicit full-type consumers; root supplies imports and audit sentinels. -/

noncomputable section
open SingularClosure
open MethbokeAddon.FDSN
open scoped BigOperators

example : (FrequencyParallel : Frequency → Frequency → Prop) =
    (fun p q => ∃ r : ℝ, ∀ j : Fin 3, (q j : ℝ) = r * (p j : ℝ)) := rfl

example : (HasActiveNoncollinearTriad : FourierCoeff → Prop) =
    (fun c => ∃ p q : Frequency,
      p ≠ 0 ∧ q ≠ 0 ∧ p + q ≠ 0 ∧ c p ≠ 0 ∧ c q ≠ 0 ∧
      c (p + q) ≠ 0 ∧ ¬ FrequencyParallel p q) := rfl

example : (transportModeTerm : FourierCoeff → Frequency → Frequency → Fin 3 → ℂ) =
    (fun c k p i => ∑ j : Fin 3, derivativeSymbol j k * c p j * c (k - p) i) := rfl

example : (meanTransportFactor : FourierCoeff → Frequency → ℂ) =
    (fun c k => ∑ j : Fin 3, derivativeSymbol j k * c 0 j) := rfl

example : ∀ (c : FourierCoeff) (k p : Frequency) (i : Fin 3),
    transportModeTerm c k p i =
      (∑ j : Fin 3, derivativeSymbol j k * c p j) * c (k - p) i :=
  @MethbokeAddon.FDSN.transportModeTerm_factored

example : ∀ (c : FourierCoeff) (p : Frequency) (i : Fin 3),
    transportModeTerm c 0 p i = 0 :=
  @MethbokeAddon.FDSN.transportModeTerm_zero_output

example : ∀ (c : FourierCoeff) (k p : Frequency) (i : Fin 3)
    (hp : c p = 0),
    transportModeTerm c k p i = 0 :=
  @MethbokeAddon.FDSN.transportModeTerm_zero_left

example : ∀ (c : FourierCoeff) (k p : Frequency) (i : Fin 3)
    (hq : c (k - p) = 0),
    transportModeTerm c k p i = 0 :=
  @MethbokeAddon.FDSN.transportModeTerm_zero_right

example : ∀ (c : FourierCoeff) (k : Frequency) (i : Fin 3),
    transportModeTerm c k 0 i = meanTransportFactor c k * c k i :=
  @MethbokeAddon.FDSN.transportModeTerm_mean

example : ∀ (c : FourierCoeff)
    (hsol : SpectralSolenoidal c) (p q : Frequency) (hpq : FrequencyParallel p q),
    (∑ j : Fin 3, derivativeSymbol j (p + q) * c p j) = 0 :=
  @MethbokeAddon.FDSN.collinear_derivativeSum_zero

example : ∀ (c : FourierCoeff) (hsol : SpectralSolenoidal c)
    (htriad : ¬ HasActiveNoncollinearTriad c)
    (k p : Frequency) (i : Fin 3) (hout : c k ≠ 0) (hp : p ≠ 0),
    transportModeTerm c k p i = 0 :=
  @MethbokeAddon.FDSN.transportModeTerm_nonzero_input_zero

example : ∀ (c : TorusSobolev 0)
    (k : Frequency) (i : Fin 3),
    HasSum (fun p : Frequency => transportModeTerm c.val k p i)
      (fullTransportCoefficients c k i) :=
  @MethbokeAddon.FDSN.fullTransportCoefficients_hasSum

example : ∀ (c : TorusSobolev 0) (hsol : SpectralSolenoidal c.val)
    (htriad : ¬ HasActiveNoncollinearTriad c.val)
    (k : Frequency) (i : Fin 3) (hout : c.val k ≠ 0),
    fullTransportCoefficients c k i = meanTransportFactor c.val k * c.val k i :=
  @MethbokeAddon.FDSN.fullTransportCoefficients_eq_mean

example : ∀ (c : FourierCoeff) (hreal : SpectralReality c)
    (j : Fin 3),
    (c 0 j).im = 0 :=
  @MethbokeAddon.FDSN.spectralReality_mean_im_zero

example : ∀ (c : FourierCoeff) (hreal : SpectralReality c)
    (k : Frequency),
    (meanTransportFactor c k).re = 0 :=
  @MethbokeAddon.FDSN.meanTransportFactor_re_zero

example : ∀ (z a : ℂ) (ha : a.re = 0),
    (star z * (a * z)).re = 0 :=
  @MethbokeAddon.FDSN.real_star_mul_imaginary

example : ∀ (c : TorusSobolev 0) (hreal : SpectralReality c.val)
    (hsol : SpectralSolenoidal c.val)
    (htriad : ¬ HasActiveNoncollinearTriad c.val)
    (k : Frequency) (i : Fin 3),
    (star (c.val k i) * fullTransportCoefficients c k i).re = 0 :=
  @MethbokeAddon.FDSN.triad_free_modal_transfer_zero

example : ∀ (c : TorusSobolev 0) (hreal : SpectralReality c.val)
    (hsol : SpectralSolenoidal c.val)
    (htriad : ¬ HasActiveNoncollinearTriad c.val)
    (S : Finset Frequency) (w : Frequency → ℝ),
    (∑ k ∈ S, w k * ∑ i : Fin 3,
      (star (c.val k i) * fullTransportCoefficients c k i).re) = 0 :=
  @MethbokeAddon.FDSN.triad_free_finite_weighted_transfer_zero

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.FrequencyParallel"
#check @MethbokeAddon.FDSN.FrequencyParallel
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.FrequencyParallel"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.FrequencyParallel"
#print axioms MethbokeAddon.FDSN.FrequencyParallel
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.FrequencyParallel"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.HasActiveNoncollinearTriad"
#check @MethbokeAddon.FDSN.HasActiveNoncollinearTriad
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.HasActiveNoncollinearTriad"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.HasActiveNoncollinearTriad"
#print axioms MethbokeAddon.FDSN.HasActiveNoncollinearTriad
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.HasActiveNoncollinearTriad"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.transportModeTerm"
#check @MethbokeAddon.FDSN.transportModeTerm
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.transportModeTerm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.transportModeTerm"
#print axioms MethbokeAddon.FDSN.transportModeTerm
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.transportModeTerm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.meanTransportFactor"
#check @MethbokeAddon.FDSN.meanTransportFactor
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.meanTransportFactor"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.meanTransportFactor"
#print axioms MethbokeAddon.FDSN.meanTransportFactor
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.meanTransportFactor"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.transportModeTerm_factored"
#check @MethbokeAddon.FDSN.transportModeTerm_factored
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.transportModeTerm_factored"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.transportModeTerm_factored"
#print axioms MethbokeAddon.FDSN.transportModeTerm_factored
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.transportModeTerm_factored"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.transportModeTerm_zero_output"
#check @MethbokeAddon.FDSN.transportModeTerm_zero_output
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.transportModeTerm_zero_output"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.transportModeTerm_zero_output"
#print axioms MethbokeAddon.FDSN.transportModeTerm_zero_output
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.transportModeTerm_zero_output"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.transportModeTerm_zero_left"
#check @MethbokeAddon.FDSN.transportModeTerm_zero_left
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.transportModeTerm_zero_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.transportModeTerm_zero_left"
#print axioms MethbokeAddon.FDSN.transportModeTerm_zero_left
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.transportModeTerm_zero_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.transportModeTerm_zero_right"
#check @MethbokeAddon.FDSN.transportModeTerm_zero_right
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.transportModeTerm_zero_right"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.transportModeTerm_zero_right"
#print axioms MethbokeAddon.FDSN.transportModeTerm_zero_right
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.transportModeTerm_zero_right"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.transportModeTerm_mean"
#check @MethbokeAddon.FDSN.transportModeTerm_mean
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.transportModeTerm_mean"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.transportModeTerm_mean"
#print axioms MethbokeAddon.FDSN.transportModeTerm_mean
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.transportModeTerm_mean"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.collinear_derivativeSum_zero"
#check @MethbokeAddon.FDSN.collinear_derivativeSum_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.collinear_derivativeSum_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.collinear_derivativeSum_zero"
#print axioms MethbokeAddon.FDSN.collinear_derivativeSum_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.collinear_derivativeSum_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.transportModeTerm_nonzero_input_zero"
#check @MethbokeAddon.FDSN.transportModeTerm_nonzero_input_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.transportModeTerm_nonzero_input_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.transportModeTerm_nonzero_input_zero"
#print axioms MethbokeAddon.FDSN.transportModeTerm_nonzero_input_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.transportModeTerm_nonzero_input_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.fullTransportCoefficients_hasSum"
#check @MethbokeAddon.FDSN.fullTransportCoefficients_hasSum
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.fullTransportCoefficients_hasSum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.fullTransportCoefficients_hasSum"
#print axioms MethbokeAddon.FDSN.fullTransportCoefficients_hasSum
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.fullTransportCoefficients_hasSum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.fullTransportCoefficients_eq_mean"
#check @MethbokeAddon.FDSN.fullTransportCoefficients_eq_mean
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.fullTransportCoefficients_eq_mean"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.fullTransportCoefficients_eq_mean"
#print axioms MethbokeAddon.FDSN.fullTransportCoefficients_eq_mean
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.fullTransportCoefficients_eq_mean"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.spectralReality_mean_im_zero"
#check @MethbokeAddon.FDSN.spectralReality_mean_im_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.spectralReality_mean_im_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.spectralReality_mean_im_zero"
#print axioms MethbokeAddon.FDSN.spectralReality_mean_im_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.spectralReality_mean_im_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.meanTransportFactor_re_zero"
#check @MethbokeAddon.FDSN.meanTransportFactor_re_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.meanTransportFactor_re_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.meanTransportFactor_re_zero"
#print axioms MethbokeAddon.FDSN.meanTransportFactor_re_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.meanTransportFactor_re_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.real_star_mul_imaginary"
#check @MethbokeAddon.FDSN.real_star_mul_imaginary
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.real_star_mul_imaginary"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.real_star_mul_imaginary"
#print axioms MethbokeAddon.FDSN.real_star_mul_imaginary
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.real_star_mul_imaginary"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triad_free_modal_transfer_zero"
#check @MethbokeAddon.FDSN.triad_free_modal_transfer_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triad_free_modal_transfer_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triad_free_modal_transfer_zero"
#print axioms MethbokeAddon.FDSN.triad_free_modal_transfer_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triad_free_modal_transfer_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triad_free_finite_weighted_transfer_zero"
#check @MethbokeAddon.FDSN.triad_free_finite_weighted_transfer_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triad_free_finite_weighted_transfer_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triad_free_finite_weighted_transfer_zero"
#print axioms MethbokeAddon.FDSN.triad_free_finite_weighted_transfer_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triad_free_finite_weighted_transfer_zero"

