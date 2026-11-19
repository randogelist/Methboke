import MethbokeAddon.EhrenfestObstruction.CrossTransport
import MethbokeAddon.EhrenfestObstruction.ProjectedReferenceEvolution
import SingularClosure.GalerkinInvariant

/-!
The literal forced coefficient equation for an actual Galerkin/reference
difference. The final theorem derives its equation from a Galerkin solution
and an actual classical front. No error evolution law is assumed there.

Prepared source: external cached compiler and axiom audit are still required.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff RealInnerProductSpace

namespace MethbokeAddon.EhrenfestObstruction

noncomputable section

theorem datumFourierCoeff_sub (a b : Field) (ha : Continuous a) (hb : Continuous b) :
    datumFourierCoeff (a - b) = datumFourierCoeff a - datumFourierCoeff b := by
  funext k i
  unfold datumFourierCoeff datumFourierIntegrand
  simp only [Pi.sub_apply, PiLp.sub_apply, Complex.ofReal_sub, mul_sub]
  exact integral_sub (datumFourierIntegrand_integrableOn ha k i)
    (datumFourierIntegrand_integrableOn hb k i)

theorem coefficientLeray_sub_arg (k : Frequency) (v w : Fin 3 → ℂ) :
    coefficientLeray k (v - w) = coefficientLeray k v - coefficientLeray k w := by
  funext i
  by_cases hk : k = 0
  · simp [coefficientLeray, hk]
  · simp only [coefficientLeray, if_neg hk, Pi.sub_apply, mul_sub,
      Finset.sum_sub_distrib, sub_div]
    ring

/-- Actual physical forcing, with reference truncation residual and both
transport cross terms. Its arguments are the reference and error coefficients. -/
def finiteReferenceErrorForcing
    (N : ℕ) (U : Field) (b w : FourierCoeff) : Field :=
  physicalErrorForcing (finiteSynthesis N b) (finiteSynthesis N w)
    (physicalReferenceResidual U (finiteSynthesis N b) (U - finiteSynthesis N b))

/-- The exact forcing field equals the difference of the actual convection
operators, after adding back the error's self convection. -/
theorem finiteReferenceErrorForcing_eq_convection
    (N : ℕ) (U : Field) (c b w : FourierCoeff)
    (hU : ContDiff ℝ ∞ U) (hsum : c = w + b) :
    finiteReferenceErrorForcing N U b w =
      convection U - convection (finiteSynthesis N c) +
        convection (finiteSynthesis N w) := by
  have hconv : convection (finiteSynthesis N c) =
      convection (finiteSynthesis N w) +
        physicalTransport (finiteSynthesis N b) (finiteSynthesis N w) +
        physicalTransport (finiteSynthesis N w) (finiteSynthesis N b) +
        convection (finiteSynthesis N b) := by
    rw [hsum, finiteSynthesis_add]
    exact convection_add_eq_transport _ _
      (finiteSynthesis_contDiff N w) (finiteSynthesis_contDiff N b)
  unfold finiteReferenceErrorForcing
  rw [physicalReferenceResidual_eq_convection_sub U (finiteSynthesis N b)
    hU (finiteSynthesis_contDiff N b), hconv]
  funext x
  simp only [physicalErrorForcing, Pi.sub_apply, Pi.add_apply]
  abel

/-- Fourier transformation of the literal forcing field. -/
theorem finiteReferenceErrorForcing_fourier
    (N : ℕ) (U : Field) (c b w : FourierCoeff)
    (hU : ContDiff ℝ ∞ U) (hsum : c = w + b)
    (hcsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c k i = 0)
    (hcreal : SpectralReality c)
    (hwsupp : ∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, w k i = 0)
    (hwreal : SpectralReality w) :
    datumFourierCoeff (finiteReferenceErrorForcing N U b w) =
      datumFourierCoeff (convection U) - coefficientTransport N c +
        coefficientTransport N w := by
  have hc := convection_continuous (finiteSynthesis_contDiff N c)
  have hw := convection_continuous (finiteSynthesis_contDiff N w)
  have hcu := convection_continuous hU
  rw [finiteReferenceErrorForcing_eq_convection N U c b w hU hsum,
    datumFourierCoeff_add _ _ (hcu.sub hc) hw,
    datumFourierCoeff_sub _ _ hcu hc,
    datumFourierCoeff_convection_finiteSynthesis N c hcsupp hcreal,
    datumFourierCoeff_convection_finiteSynthesis N w hwsupp hwreal]

/-- Subtracting the projected reference vector field from the actual finite
NSE vector field gives the error vector field plus its literal forcing. -/
theorem finite_error_rhs_identity
    (ν : ℝ) (N : ℕ) (U : Field) (c b w : FourierCoeff)
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
          (datumFourierCoeff (finiteReferenceErrorForcing N U b w) l)) k i := by
  rw [cutoffCoeff_apply_of_mem _ hk i,
    finiteReferenceErrorForcing_fourier N U c b w hU hsum hcsupp hcreal hwsupp hwreal]
  simp only [galerkinRhs, Pi.add_apply, Pi.sub_apply,
    coefficientLeray_add_arg, coefficientLeray_sub_arg]
  have hmode : c k i = w k i + b k i :=
    congrArg (fun d : FourierCoeff => d k i) hsum
  rw [hmode]
  ring

/-- An actual Galerkin solution minus the actual projected classical front
satisfies the forced error equation at every interior reference time. -/
theorem initial_front_galerkin_error_hasDerivAt
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
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
            (g.coeff t - cutoffCoeff N (datumFourierCoeff (u t)))) l)) k i) t := by
  let b : ℝ → FourierCoeff := fun r => cutoffCoeff N (datumFourierCoeff (u r))
  let w : FourierCoeff := g.coeff t - b t
  have hU := initial_front_smooth_slices ν S a u p H t ⟨ht.1.le, ht.2⟩
  have hbreal : SpectralReality (b t) :=
    cutoffCoeff_preserves_reality N (datumFourierCoeff_reality (u t))
  have hwsupp : ∀ l : Frequency, l ∉ cutoffModes N → ∀ j : Fin 3, w l j = 0 := by
    intro l hl j
    change g.coeff t l j - cutoffCoeff N (datumFourierCoeff (u t)) l j = 0
    rw [g.mode_support t ht.1.le l hl j, cutoffCoeff_apply_of_not_mem _ hl j]
    simp
  have hwreal : SpectralReality w := by
    intro l j
    change g.coeff t (-l) j - b t (-l) j = star (g.coeff t l j - b t l j)
    rw [g.real_symmetry t ht.1.le l j, hbreal l j, star_sub]
  have hsum : g.coeff t = w + b t := by
    dsimp [w]
    simp
  have hg := (g.equation t ht.1.le k hk i).hasDerivAt (Ici_mem_nhds ht.1)
  have hb : HasDerivAt (fun r => b r k i)
      (-((ν * (2 * Real.pi) ^ 2 * (galerkinFreqSq k : ℝ) : ℝ) : ℂ) * b t k i -
        coefficientLeray k (datumFourierCoeff (convection (u t)) k) i) t := by
    simpa only [b, cutoffCoeff, if_pos hk] using
      initial_front_cutoff_fourier_hasDerivAt ν S a u p H N k i t ht
  have hd := hg.sub hb
  rw [finite_error_rhs_identity ν N (u t) (g.coeff t) (b t) w hU.smooth hsum
    (g.mode_support t ht.1.le) (g.real_symmetry t ht.1.le) hwsupp hwreal k hk i] at hd
  exact hd

end

end MethbokeAddon.EhrenfestObstruction
