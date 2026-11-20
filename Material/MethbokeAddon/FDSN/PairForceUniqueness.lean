import MethbokeAddon.FDSN.PairTransport
import MethbokeAddon.FDSN.ForcedFourierEvolution

/-!
# Selected-mode uniqueness for a one-pair perturbation

The hypotheses concern two actual preterminal forced Navier--Stokes fields.
The nonlinear difference is evaluated from their actual Fourier coefficients,
and equal projected forcing gives a damped scalar ODE at the selected mode.
Its imaginary mean-advection coefficient is retained. This is sufficient to
separate the projected force histories of distinct localized phase rotations.
-/

set_option autoImplicit false

noncomputable section
open Set SingularClosure
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

theorem spectralSolenoidal_sub (c d : FourierCoeff)
    (hc : SpectralSolenoidal c) (hd : SpectralSolenoidal d) :
    SpectralSolenoidal (c - d) := by
  intro k
  change (∑ j : Fin 3, (k j : ℂ) * (c k j - d k j)) = 0
  simp only [mul_sub, Finset.sum_sub_distrib, hc k, hd k, sub_self]

theorem coefficientLeray_sub_arg (k : Frequency) (v w : Fin 3 → ℂ) :
    coefficientLeray k (v - w) = coefficientLeray k v - coefficientLeray k w := by
  calc
    coefficientLeray k (v - w) = coefficientLeray k (v + (-1 : ℂ) • w) := by
      rw [neg_one_smul, sub_eq_add_neg]
    _ = coefficientLeray k v + (-1 : ℂ) • coefficientLeray k w := by
      rw [coefficientLeray_add_arg, coefficientLeray_smul_arg]
    _ = coefficientLeray k v - coefficientLeray k w := by
      rw [neg_one_smul, sub_eq_add_neg]

/-- Leray projection retains precisely the mean-advection term in the
nonlinear difference at the selected mode. -/
theorem projectedTransport_pair_difference
    (c d : TorusSobolev 0) (a : Frequency) (i : Fin 3)
    (hc : SpectralSolenoidal c.val) (hd : SpectralSolenoidal d.val)
    (hsupp : PairSupported a (d.val - c.val)) :
    coefficientLeray a (fullTransportCoefficients d a) i -
        coefficientLeray a (fullTransportCoefficients c a) i =
      meanTransportFactor c.val a * (d.val a i - c.val a i) := by
  have hh : SpectralSolenoidal (d - c).val :=
    spectralSolenoidal_sub d.val c.val hd hc
  have hadd : c + (d - c) = d :=
    (add_comm c (d - c)).trans (sub_add_cancel d c)
  have hraw : fullTransportCoefficients d a - fullTransportCoefficients c a =
      meanTransportFactor c.val a • (d - c).val a := by
    funext j
    simpa only [hadd] using
      fullTransport_pair_difference c (d - c) a j hc hh hsupp
  calc
    coefficientLeray a (fullTransportCoefficients d a) i -
          coefficientLeray a (fullTransportCoefficients c a) i =
        coefficientLeray a
          (fullTransportCoefficients d a - fullTransportCoefficients c a) i :=
      (congrFun (coefficientLeray_sub_arg a
        (fullTransportCoefficients d a) (fullTransportCoefficients c a)) i).symm
    _ = meanTransportFactor c.val a * (d.val a i - c.val a i) := by
      rw [hraw, coefficientLeray_smul_arg,
        coefficientLeray_eq_of_solenoidal a _ (hh a)]
      rfl

/-- The selected coefficient difference of two actual PDE fronts satisfies
a damped ODE whenever their projected forces agree in that component. -/
theorem PreterminalNSE.pair_difference_hasDerivAt
    {ν T : ℝ} {u v F G : Velocity} {p q : Pressure}
    (H : PreterminalNSE ν T u p F) (K : PreterminalNSE ν T v q G)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T)
    (hF : Continuous (F t)) (hG : Continuous (G t))
    (a : Frequency) (i : Fin 3)
    (hsupp : PairSupported a (datumFourierCoeff (v t) - datumFourierCoeff (u t)))
    (hforce : coefficientLeray a (datumFourierCoeff (G t) a) i =
      coefficientLeray a (datumFourierCoeff (F t) a) i) :
    HasDerivAt
      (fun r => datumFourierCoeff (v r) a i - datumFourierCoeff (u r) a i)
      (-(((ν * laplacianFrequency a : ℝ) : ℂ) +
          meanTransportFactor (datumFourierCoeff (u t)) a) *
        (datumFourierCoeff (v t) a i - datumFourierCoeff (u t) a i)) t := by
  have hN := projectedTransport_pair_difference
    (H.sobolevSlice t ht) (K.sobolevSlice t ht) a i
    (H.fourier_solenoidal t ht) (K.fourier_solenoidal t ht) hsupp
  change coefficientLeray a (fullTransportCoefficients (K.sobolevSlice t ht) a) i -
      coefficientLeray a (fullTransportCoefficients (H.sobolevSlice t ht) a) i =
    meanTransportFactor (datumFourierCoeff (u t)) a *
      (datumFourierCoeff (v t) a i - datumFourierCoeff (u t) a i) at hN
  have hd := (K.projected_fourier_hasDerivAt t ht hG a i).sub
    (H.projected_fourier_hasDerivAt t ht hF a i)
  have hrate :
      (-((ν * laplacianFrequency a : ℝ) : ℂ) * datumFourierCoeff (v t) a i -
          coefficientLeray a (fullTransportCoefficients (K.sobolevSlice t ht) a) i +
          coefficientLeray a (datumFourierCoeff (G t) a) i) -
        (-((ν * laplacianFrequency a : ℝ) : ℂ) * datumFourierCoeff (u t) a i -
          coefficientLeray a (fullTransportCoefficients (H.sobolevSlice t ht) a) i +
          coefficientLeray a (datumFourierCoeff (F t) a) i) =
        -(((ν * laplacianFrequency a : ℝ) : ℂ) +
          meanTransportFactor (datumFourierCoeff (u t)) a) *
          (datumFourierCoeff (v t) a i - datumFourierCoeff (u t) a i) := by
    rw [hforce]
    linear_combination -hN
  simpa only [hrate] using hd

/-- A one-pair difference cannot first develop a nonzero selected mode while
the corresponding projected-force component remains equal. -/
theorem PreterminalNSE.pair_mode_eq_on_Icc
    {ν T : ℝ} {u v F G : Velocity} {p q : Pressure}
    (H : PreterminalNSE ν T u p F) (K : PreterminalNSE ν T v q G)
    (hν : 0 ≤ ν) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (a : Frequency) (i : Fin 3)
    (hF : ∀ r ∈ Ioo s t, Continuous (F r))
    (hG : ∀ r ∈ Ioo s t, Continuous (G r))
    (hsupp : ∀ r ∈ Ioo s t,
      PairSupported a (datumFourierCoeff (v r) - datumFourierCoeff (u r)))
    (hforce : ∀ r ∈ Ioo s t,
      coefficientLeray a (datumFourierCoeff (G r) a) i =
        coefficientLeray a (datumFourierCoeff (F r) a) i)
    (hinit : datumFourierCoeff (v s) a i = datumFourierCoeff (u s) a i) :
    ∀ r ∈ Icc s t, datumFourierCoeff (v r) a i = datumFourierCoeff (u r) a i := by
  let z : ℝ → ℂ :=
    fun r => datumFourierCoeff (v r) a i - datumFourierCoeff (u r) a i
  let damping : ℝ → ℂ := fun r => ((ν * laplacianFrequency a : ℝ) : ℂ) +
    meanTransportFactor (datumFourierCoeff (u r)) a
  have hinside (r : ℝ) (hr : r ∈ Icc s t) : r ∈ Ioo (0 : ℝ) T :=
    ⟨lt_of_lt_of_le hs hr.1, lt_of_le_of_lt hr.2 ht⟩
  have hc : ContinuousOn z (Icc s t) := by
    intro r hr
    exact ((K.fourierCoeff_hasDerivAt r (hinside r hr) a i).sub
      (H.fourierCoeff_hasDerivAt r (hinside r hr) a i)).continuousAt.continuousWithinAt
  have hd : ∀ r ∈ Ioo s t, HasDerivAt z (-damping r * z r) r := by
    intro r hr
    exact H.pair_difference_hasDerivAt K r (hinside r ⟨hr.1.le, hr.2.le⟩)
      (hF r hr) (hG r hr) a i (hsupp r hr) (hforce r hr)
  have ha : ∀ r ∈ Ioo s t, 0 ≤ (damping r).re := by
    intro r _
    dsimp only [damping]
    rw [Complex.add_re, Complex.ofReal_re,
      meanTransportFactor_re_zero _ (datumFourierCoeff_reality (u r)) a, add_zero]
    exact mul_nonneg hν (laplacianFrequency_nonneg a)
  have hz : z s = 0 := sub_eq_zero.mpr hinit
  have he := complex_damped_zero_on_Icc z damping s t hst hc hd ha hz
  intro r hr
  exact sub_eq_zero.mp (he r hr)

/-- Distinct selected modes after a shared initial slice force an actual
difference in the projected force history at an interior time. -/
theorem PreterminalNSE.projected_force_ne_of_pair_mode_ne
    {ν T : ℝ} {u v F G : Velocity} {p q : Pressure}
    (H : PreterminalNSE ν T u p F) (K : PreterminalNSE ν T v q G)
    (hν : 0 ≤ ν) (s t : ℝ) (hs : 0 < s) (hst : s ≤ t) (ht : t < T)
    (a : Frequency) (i : Fin 3)
    (hF : ∀ r ∈ Ioo s t, Continuous (F r))
    (hG : ∀ r ∈ Ioo s t, Continuous (G r))
    (hsupp : ∀ r ∈ Ioo s t,
      PairSupported a (datumFourierCoeff (v r) - datumFourierCoeff (u r)))
    (hinit : datumFourierCoeff (v s) a i = datumFourierCoeff (u s) a i)
    (hfinal : datumFourierCoeff (v t) a i ≠ datumFourierCoeff (u t) a i) :
    ∃ r ∈ Ioo s t,
      coefficientLeray a (datumFourierCoeff (G r) a) i ≠
        coefficientLeray a (datumFourierCoeff (F r) a) i := by
  classical
  by_contra hnone
  have hforce : ∀ r ∈ Ioo s t,
      coefficientLeray a (datumFourierCoeff (G r) a) i =
        coefficientLeray a (datumFourierCoeff (F r) a) i := by
    intro r hr
    by_contra hne
    exact hnone ⟨r, hr, hne⟩
  exact hfinal (H.pair_mode_eq_on_Icc K hν s t hs hst ht a i
    hF hG hsupp hforce hinit t ⟨hst, le_rfl⟩)

end MethbokeAddon.FDSN
