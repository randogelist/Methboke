import MethbokeAddon.FDSN.TriadCancellation

/-!
# Exact mixed-transport cancellation at a one-pair perturbation mode

The coefficient of the nonlinear difference at the selected mode is
exactly mean advection. This is the spatial Fourier algebra needed for
construction-specific projected-force separation.
-/

noncomputable section

open SingularClosure
open scoped BigOperators

namespace MethbokeAddon.FDSN

def PairSupported (a : Frequency) (h : FourierCoeff) : Prop :=
  ∀ p : Frequency, p ≠ a → p ≠ -a → h p = 0

def mixedTransportModeTerm (c d : FourierCoeff) (k p : Frequency) (i : Fin 3) : ℂ :=
  ∑ j : Fin 3, derivativeSymbol j k * c p j * d (k - p) i

theorem mixedTransportModeTerm_factored
    (c d : FourierCoeff) (k p : Frequency) (i : Fin 3) :
    mixedTransportModeTerm c d k p i =
      (∑ j : Fin 3, derivativeSymbol j k * c p j) * d (k - p) i := by
  simp only [mixedTransportModeTerm, Finset.sum_mul]

theorem divergenceTransportCoefficient_hasSum
    (c d : TorusSobolev 0) (k : Frequency) (i : Fin 3) :
    HasSum (fun p : Frequency => mixedTransportModeTerm c.val d.val k p i)
      (divergenceTransportCoefficient k i c d) := by
  have hs : HasSum
      (fun p : Frequency => ∑ j : Fin 3,
        derivativeSymbol j k * (c.val p j * d.val (k - p) i))
      (∑ j : Fin 3, derivativeSymbol j k *
        (∑' p : Frequency, c.val p j * d.val (k - p) i)) := by
    exact hasSum_sum (fun j _ =>
      (fourierTensorCoefficient_summable k j i c d).hasSum.mul_left (derivativeSymbol j k))
  simpa only [mixedTransportModeTerm, divergenceTransportCoefficient_apply, mul_assoc] using hs

theorem solenoidal_derivativeSum_at_negative
    (c : FourierCoeff) (hsol : SpectralSolenoidal c) (a : Frequency) :
    (∑ j : Fin 3, derivativeSymbol j a * c (-a) j) = 0 := by
  have hp : FrequencyParallel (-a) (a + a) := by
    refine ⟨-2, ?_⟩
    intro j
    simp only [Pi.add_apply, Pi.neg_apply, Int.cast_add, Int.cast_neg]
    ring
  have hs : -a + (a + a) = a := by
    funext j
    change -(a j) + (a j + a j) = a j
    omega
  simpa only [hs] using collinear_derivativeSum_zero c hsol (-a) (a + a) hp

theorem solenoidal_derivativeSum_at_double
    (c : FourierCoeff) (hsol : SpectralSolenoidal c) (a : Frequency) :
    (∑ j : Fin 3, derivativeSymbol j a * c (a + a) j) = 0 := by
  have hder (j : Fin 3) : derivativeSymbol j (a + a) = 2 * derivativeSymbol j a := by
    simp only [derivativeSymbol, Pi.add_apply, Int.cast_add]
    push_cast
    ring
  have hs : (2 : ℂ) * (∑ j : Fin 3, derivativeSymbol j a * c (a + a) j) = 0 := by
    simpa only [hder, Finset.mul_sum, mul_assoc] using
      solenoidal_derivativeSymbol_sum c hsol (a + a)
  exact (mul_eq_zero.mp hs).resolve_left (by norm_num)

/-- A solenoidal one-pair field advects any background with zero output
coefficient at its selected mode. -/
theorem divergenceTransport_pair_left
    (h c : TorusSobolev 0) (a : Frequency) (i : Fin 3)
    (hsol : SpectralSolenoidal h.val) (hsupp : PairSupported a h.val) :
    divergenceTransportCoefficient a i h c = 0 := by
  classical
  have hterm (p : Frequency) : mixedTransportModeTerm h.val c.val a p i = 0 := by
    by_cases hp : p = a
    · subst p
      rw [mixedTransportModeTerm_factored,
        solenoidal_derivativeSymbol_sum h.val hsol a, zero_mul]
    by_cases hn : p = -a
    · subst p
      rw [mixedTransportModeTerm_factored,
        solenoidal_derivativeSum_at_negative h.val hsol a, zero_mul]
    simp [mixedTransportModeTerm, hsupp p hp hn]
  calc
    divergenceTransportCoefficient a i h c =
        ∑' p : Frequency, mixedTransportModeTerm h.val c.val a p i :=
      (divergenceTransportCoefficient_hasSum h c a i).tsum_eq.symm
    _ = 0 := by simp only [hterm, tsum_zero]

/-- A solenoidal background advects a one-pair perturbation at its selected
mode only through its spatial mean. -/
theorem divergenceTransport_pair_right
    (c h : TorusSobolev 0) (a : Frequency) (i : Fin 3)
    (hsol : SpectralSolenoidal c.val) (hsupp : PairSupported a h.val) :
    divergenceTransportCoefficient a i c h =
      meanTransportFactor c.val a * h.val a i := by
  classical
  have hterm (p : Frequency) (hp : p ≠ 0) :
      mixedTransportModeTerm c.val h.val a p i = 0 := by
    by_cases hd : p = a + a
    · subst p
      rw [mixedTransportModeTerm_factored,
        solenoidal_derivativeSum_at_double c.val hsol a, zero_mul]
    have hqa : a - p ≠ a := by
      intro he
      apply hp
      funext j
      have hj := congrFun he j
      change a j - p j = a j at hj
      change p j = 0
      omega
    have hqn : a - p ≠ -a := by
      intro he
      apply hd
      funext j
      have hj := congrFun he j
      change a j - p j = -(a j) at hj
      change p j = a j + a j
      omega
    simp [mixedTransportModeTerm, hsupp (a - p) hqa hqn]
  have hs : HasSum (fun p : Frequency => mixedTransportModeTerm c.val h.val a p i)
      (mixedTransportModeTerm c.val h.val a 0 i) := hasSum_single 0 hterm
  calc
    divergenceTransportCoefficient a i c h = mixedTransportModeTerm c.val h.val a 0 i :=
      (divergenceTransportCoefficient_hasSum c h a i).unique hs
    _ = meanTransportFactor c.val a * h.val a i := by
      rw [mixedTransportModeTerm_factored]
      simp only [meanTransportFactor, sub_zero]

/-- Exact nonlinear difference at the selected mode of a solenoidal
one-pair perturbation. All non-mean interaction terms have been eliminated. -/
theorem fullTransport_pair_difference
    (c h : TorusSobolev 0) (a : Frequency) (i : Fin 3)
    (hc : SpectralSolenoidal c.val) (hh : SpectralSolenoidal h.val)
    (hsupp : PairSupported a h.val) :
    fullTransportCoefficients (c + h) a i - fullTransportCoefficients c a i =
      meanTransportFactor c.val a * h.val a i := by
  simp only [fullTransportCoefficients, map_add, ContinuousLinearMap.add_apply]
  rw [divergenceTransport_pair_right c h a i hc hsupp,
    divergenceTransport_pair_left h c a i hh hsupp,
    divergenceTransport_pair_left h h a i hh hsupp]
  ring

/-- The nonlinear difference contributes no real perturbation energy at
the selected mode, including for a nonzero spatial mean. -/
theorem fullTransport_pair_difference_real_transfer_zero
    (c h : TorusSobolev 0) (a : Frequency) (i : Fin 3)
    (hreal : SpectralReality c.val) (hc : SpectralSolenoidal c.val)
    (hh : SpectralSolenoidal h.val) (hsupp : PairSupported a h.val) :
    (star (h.val a i) *
      (fullTransportCoefficients (c + h) a i - fullTransportCoefficients c a i)).re = 0 := by
  rw [fullTransport_pair_difference c h a i hc hh hsupp]
  exact real_star_mul_imaginary _ _ (meanTransportFactor_re_zero c.val hreal a)

end MethbokeAddon.FDSN
