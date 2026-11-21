import MethbokeAddon.QuasiFeffermanA.RealFourier
import Mathlib.Analysis.Fourier.FourierTransformDeriv
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Actual L1 inverse representatives of native L2 Fourier classes

For a native complex L2 field whose chosen frequency representative is
integrable, the inverse Fourier integral agrees almost everywhere with the
native L2 inverse. The proof uses Fourier compatibility in tempered
distributions, the integrable Fourier Fubini theorem, and compact-test
uniqueness. It does not assume the desired representative agreement.

Polynomial L1 moments are an elementary sufficient condition for smoothness
of that same bounded continuous representative. A separate cutoff module
will construct all such moments from finite frequency-ball support.

Prepared source only: matching authorized cached external compilation and
named type/axiom evidence are required. No local Lean, Lake or kernel run.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff BoundedContinuousFunction

namespace MethbokeAddon.R3Ehrenfest.FourierL1L2

open MethbokeAddon.QuasiFeffermanA
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)

/-- The literal bounded continuous inverse Fourier integral. -/
def inverseL1Representative (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume) : Space →ᵇ ComplexVector :=
  Real.Lp.fourierTransformInv
    (hf.memLp_one.toLp (fun ξ : Space => f ξ))

theorem inverseL1Representative_apply (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume) (x : Space) :
    inverseL1Representative f hf x = (𝓕⁻ (fun ξ : Space => f ξ)) x := by
  exact congrFun (Real.Lp.fourierTransformInv_toLp hf.memLp_one) x

theorem continuous_fourierInv_integral (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume) :
    Continuous (𝓕⁻ (fun ξ : Space => f ξ)) := by
  have he : (fun x : Space => inverseL1Representative f hf x) =
      𝓕⁻ (fun ξ : Space => f ξ) :=
    funext (inverseL1Representative_apply f hf)
  rw [← he]
  exact (inverseL1Representative f hf).continuous

private theorem real_smul_complexVector (r : ℝ) (z : ComplexVector) :
    r • z = (r : ℂ) • z := by
  apply PiLp.ext
  intro j
  change r • z j = (r : ℂ) * z j
  exact Complex.real_smul

private theorem integral_inverse_test_swap (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume) (test : 𝓢(Space, ℂ)) :
    (∫ x : Space, test x • (𝓕⁻ (fun ξ : Space => f ξ)) x) =
      ∫ ξ : Space, (𝓕⁻ test) ξ • f ξ := by
  have hflip : (-innerₗ Space).flip = -innerₗ Space := by
    ext x y
    change -(inner ℝ y x) = -(inner ℝ x y)
    rw [real_inner_comm]
  have h := VectorFourier.integral_fourierIntegral_smul_eq_flip
    (e := Real.fourierChar) (L := -innerₗ Space)
    Real.continuous_fourierChar
    (by
      change Continuous (fun p : Space × Space => -(inner ℝ p.1 p.2))
      fun_prop)
    test.integrable hf
  rw [hflip] at h
  change (∫ ξ : Space, (𝓕⁻ (test : Space → ℂ)) ξ • f ξ) =
    ∫ x : Space, test x • (𝓕⁻ (fun ξ : Space => f ξ)) x at h
  simpa only [SchwartzMap.fourierInv_coe] using h.symm

/-- The inverse Fourier integral is a representative of the actual native
L2 inverse. Agreement is proved from the two existing Fourier constructions. -/
theorem fourierInv_integral_ae (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume) :
    (𝓕⁻ (fun ξ : Space => f ξ)) =ᵐ[volume]
      (fun x : Space => (𝓕⁻ f : ComplexL2) x) := by
  apply ae_eq_of_integral_contDiff_smul_eq
  · exact (continuous_fourierInv_integral f hf).locallyIntegrable
  · exact (Lp.memLp (𝓕⁻ f : ComplexL2)).locallyIntegrable (by norm_num)
  · intro g hg hcpt
    have ht_cpt : HasCompactSupport (Complex.ofRealCLM ∘ g) := hcpt.comp_left rfl
    have ht_smooth : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
    let test : 𝓢(Space, ℂ) := ht_cpt.toSchwartzMap ht_smooth
    have htest (x : Space) : test x = (g x : ℂ) := rfl
    have heval := congrArg (fun T : 𝓢'(Space, ComplexVector) => T test)
      (Lp.fourierInv_toTemperedDistribution_eq f)
    have hpair : (∫ ξ : Space, (𝓕⁻ test) ξ • f ξ) =
        ∫ x : Space, test x • (𝓕⁻ f : ComplexL2) x := by
      simpa only [TemperedDistribution.fourierInv_apply,
        Lp.toTemperedDistribution_apply] using heval
    calc
      (∫ x : Space, g x • (𝓕⁻ (fun ξ : Space => f ξ)) x) =
          ∫ x : Space, test x • (𝓕⁻ (fun ξ : Space => f ξ)) x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [htest]
        exact real_smul_complexVector _ _
      _ = ∫ ξ : Space, (𝓕⁻ test) ξ • f ξ :=
        integral_inverse_test_swap f hf test
      _ = ∫ x : Space, test x • (𝓕⁻ f : ComplexL2) x := hpair
      _ = ∫ x : Space, g x • (𝓕⁻ f : ComplexL2) x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [htest]
        exact (real_smul_complexVector _ _).symm

theorem inverseL1Representative_ae (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume) :
    (fun x : Space => inverseL1Representative f hf x) =ᵐ[volume]
      (fun x : Space => (𝓕⁻ f : ComplexL2) x) := by
  simpa only [inverseL1Representative_apply] using fourierInv_integral_ae f hf

theorem norm_inverseL1Representative_le (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume) :
    ‖inverseL1Representative f hf‖ ≤
      ‖Real.Lp.fourierTransformInvCLM Space ComplexVector‖ *
        ‖hf.memLp_one.toLp (fun ξ : Space => f ξ)‖ :=
  (Real.Lp.fourierTransformInvCLM Space ComplexVector).le_opNorm _

/-- Every polynomial L1 moment yields smoothness of the same actual inverse
representative. Finite frequency support will supply these moments. -/
theorem contDiff_inverseL1Representative (f : ComplexL2)
    (hf : Integrable (fun ξ : Space => f ξ) volume)
    (hm : ∀ k : ℕ, Integrable (fun ξ : Space => ‖ξ‖ ^ k * ‖f ξ‖) volume) :
    ContDiff ℝ ∞ (fun x : Space => inverseL1Representative f hf x) := by
  have hF : ContDiff ℝ ∞ (𝓕 (fun ξ : Space => f ξ)) :=
    Real.contDiff_fourier (N := (⊤ : ℕ∞)) (fun k _ => hm k)
  have he : (fun x : Space => inverseL1Representative f hf x) =
      (fun x : Space => (𝓕 (fun ξ : Space => f ξ)) (-x)) := by
    funext x
    rw [inverseL1Representative_apply, Real.fourierInv_eq_fourier_neg]
  rw [he]
  exact hF.comp contDiff_neg

end MethbokeAddon.R3Ehrenfest.FourierL1L2

