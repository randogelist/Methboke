import FDSNForcedFourierEvolution.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/- Explicit full-type consumers; root supplies imports and audit sentinels. -/

noncomputable section
open Set SingularClosure
open MethbokeAddon.FDSN MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff

example {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (H : PreterminalNSE ν T u p F) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    H.sobolevSlice t ht =
      smoothDatumSobolev 0 (u t) (H.velocity_slice_smooth t ht)
        (H.velocity_periodic t ⟨ht.1.le, ht.2⟩) := rfl

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T),
    ContDiff ℝ ∞ (u t) :=
  @MethbokeAddon.FDSN.PreterminalNSE.velocity_slice_smooth

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T),
    ContDiff ℝ ∞ (p t) :=
  @MethbokeAddon.FDSN.PreterminalNSE.pressure_slice_smooth

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T),
    SpectralSolenoidal (datumFourierCoeff (u t)) :=
  @MethbokeAddon.FDSN.PreterminalNSE.fourier_solenoidal

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T),
    (H.sobolevSlice t ht).val = datumFourierCoeff (u t) :=
  @MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice_coeff

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T),
    datumFourierCoeff (convection (u t)) =
      fullTransportCoefficients (H.sobolevSlice t ht) :=
  @MethbokeAddon.FDSN.PreterminalNSE.convection_coeff

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (k : Frequency) (i : Fin 3),
    HasDerivAt (fun r => datumFourierCoeff (u r) k i)
      (datumFourierCoeff (timeDerivative u t) k i) t :=
  @MethbokeAddon.FDSN.PreterminalNSE.fourierCoeff_hasDerivAt

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T),
    SpectralSolenoidal (datumFourierCoeff (timeDerivative u t)) :=
  @MethbokeAddon.FDSN.PreterminalNSE.timeDerivative_fourier_solenoidal

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (hF : Continuous (F t)) (k : Frequency),
    datumFourierCoeff (timeDerivative u t) k +
        fullTransportCoefficients (H.sobolevSlice t ht) k +
        (fun i => derivativeSymbol i k * scalarPressureFourierCoeff (p t) k) =
      (ν : ℂ) • laplacianCoefficient (datumFourierCoeff (u t)) k +
        datumFourierCoeff (F t) k :=
  @MethbokeAddon.FDSN.PreterminalNSE.fourier_balance

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (hF : Continuous (F t)) (k : Frequency),
    datumFourierCoeff (timeDerivative u t) k +
        coefficientLeray k (fullTransportCoefficients (H.sobolevSlice t ht) k) =
      (ν : ℂ) • laplacianCoefficient (datumFourierCoeff (u t)) k +
        coefficientLeray k (datumFourierCoeff (F t) k) :=
  @MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_balance

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (hF : Continuous (F t))
    (k : Frequency) (i : Fin 3),
    HasDerivAt (fun r => datumFourierCoeff (u r) k i)
      (-((ν * laplacianFrequency k : ℝ) : ℂ) * datumFourierCoeff (u t) k i -
        coefficientLeray k (fullTransportCoefficients (H.sobolevSlice t ht) k) i +
        coefficientLeray k (datumFourierCoeff (F t) k) i) t :=
  @MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_hasDerivAt

example : ∀ (c : TorusSobolev 0) (hreal : SpectralReality c.val)
    (hsol : SpectralSolenoidal c.val) (htriad : ¬ HasActiveNoncollinearTriad c.val)
    (k : Frequency) (i : Fin 3),
    (star (c.val k i) * coefficientLeray k (fullTransportCoefficients c k) i).re = 0 :=
  @MethbokeAddon.FDSN.triad_free_projected_modal_transfer_zero

example : ∀ (k : Frequency),
    0 ≤ laplacianFrequency k :=
  @MethbokeAddon.FDSN.laplacianFrequency_nonneg

example : ∀ {ν T : ℝ} {u F : Velocity} {p : Pressure} (H : PreterminalNSE ν T u p F)
    (hν : 0 ≤ ν) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) (hF : Continuous (F t))
    (htriad : ¬ HasActiveNoncollinearTriad (datumFourierCoeff (u t)))
    (k : Frequency) (i : Fin 3),
    deriv (fun r => Complex.normSq (datumFourierCoeff (u r) k i)) t ≤
      Complex.normSq (datumFourierCoeff (u t) k i) +
        Complex.normSq (coefficientLeray k (datumFourierCoeff (F t) k) i) :=
  @MethbokeAddon.FDSN.PreterminalNSE.triad_free_mode_energy_bound

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.velocity_slice_smooth"
#check @MethbokeAddon.FDSN.PreterminalNSE.velocity_slice_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.velocity_slice_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.velocity_slice_smooth"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.velocity_slice_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.velocity_slice_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.pressure_slice_smooth"
#check @MethbokeAddon.FDSN.PreterminalNSE.pressure_slice_smooth
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.pressure_slice_smooth"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.pressure_slice_smooth"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.pressure_slice_smooth
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.pressure_slice_smooth"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.fourier_solenoidal"
#check @MethbokeAddon.FDSN.PreterminalNSE.fourier_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.fourier_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.fourier_solenoidal"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.fourier_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.fourier_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice"
#check @MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice_coeff"
#check @MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice_coeff
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice_coeff"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.sobolevSlice_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.convection_coeff"
#check @MethbokeAddon.FDSN.PreterminalNSE.convection_coeff
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.convection_coeff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.convection_coeff"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.convection_coeff
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.convection_coeff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.fourierCoeff_hasDerivAt"
#check @MethbokeAddon.FDSN.PreterminalNSE.fourierCoeff_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.fourierCoeff_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.fourierCoeff_hasDerivAt"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.fourierCoeff_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.fourierCoeff_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.timeDerivative_fourier_solenoidal"
#check @MethbokeAddon.FDSN.PreterminalNSE.timeDerivative_fourier_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.timeDerivative_fourier_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.timeDerivative_fourier_solenoidal"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.timeDerivative_fourier_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.timeDerivative_fourier_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.fourier_balance"
#check @MethbokeAddon.FDSN.PreterminalNSE.fourier_balance
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.fourier_balance"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.fourier_balance"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.fourier_balance
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.fourier_balance"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_balance"
#check @MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_balance
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_balance"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_balance"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_balance
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_balance"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_hasDerivAt"
#check @MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_hasDerivAt"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.projected_fourier_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.triad_free_projected_modal_transfer_zero"
#check @MethbokeAddon.FDSN.triad_free_projected_modal_transfer_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.triad_free_projected_modal_transfer_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.triad_free_projected_modal_transfer_zero"
#print axioms MethbokeAddon.FDSN.triad_free_projected_modal_transfer_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.triad_free_projected_modal_transfer_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.laplacianFrequency_nonneg"
#check @MethbokeAddon.FDSN.laplacianFrequency_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.laplacianFrequency_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.laplacianFrequency_nonneg"
#print axioms MethbokeAddon.FDSN.laplacianFrequency_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.laplacianFrequency_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.triad_free_mode_energy_bound"
#check @MethbokeAddon.FDSN.PreterminalNSE.triad_free_mode_energy_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE.triad_free_mode_energy_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE.triad_free_mode_energy_bound"
#print axioms MethbokeAddon.FDSN.PreterminalNSE.triad_free_mode_energy_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE.triad_free_mode_energy_bound"

