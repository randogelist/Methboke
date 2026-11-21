import R3EhrenfestFourierL1L2.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform SchwartzMap ContDiff BoundedContinuousFunction

namespace R3EhrenfestFourierL1L2.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealFourier
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open MethbokeAddon.R3Ehrenfest.FourierL1L2

-- Literal whole-space domain and native L2 measure.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl

-- Integrability is the elementary visible premise; no a.e. reconstruction is supplied.
example (f : ComplexL2) (hf : Integrable (fun ξ : Space => f ξ) volume) :
    Space →ᵇ ComplexVector := inverseL1Representative f hf
example (f : ComplexL2) (hf : Integrable (fun ξ : Space => f ξ) volume) (x : Space) :
    inverseL1Representative f hf x = (𝓕⁻ (fun ξ : Space => f ξ)) x :=
  inverseL1Representative_apply f hf x
example (f : ComplexL2) (hf : Integrable (fun ξ : Space => f ξ) volume) :
    Continuous (𝓕⁻ (fun ξ : Space => f ξ)) := continuous_fourierInv_integral f hf
example (f : ComplexL2) (hf : Integrable (fun ξ : Space => f ξ) volume) :
    (𝓕⁻ (fun ξ : Space => f ξ)) =ᵐ[volume]
      (fun x : Space => (𝓕⁻ f : ComplexL2) x) := fourierInv_integral_ae f hf
example (f : ComplexL2) (hf : Integrable (fun ξ : Space => f ξ) volume) :
    (fun x : Space => inverseL1Representative f hf x) =ᵐ[volume]
      (fun x : Space => (𝓕⁻ f : ComplexL2) x) := inverseL1Representative_ae f hf
example (f : ComplexL2) (hf : Integrable (fun ξ : Space => f ξ) volume) :
    ‖inverseL1Representative f hf‖ ≤
      ‖Real.Lp.fourierTransformInvCLM Space ComplexVector‖ *
        ‖hf.memLp_one.toLp (fun ξ : Space => f ξ)‖ :=
  norm_inverseL1Representative_le f hf

-- Smoothness uses actual polynomial L1 moments, without a smoothness input.
example (f : ComplexL2) (hf : Integrable (fun ξ : Space => f ξ) volume)
    (hm : ∀ k : ℕ, Integrable (fun ξ : Space => ‖ξ‖ ^ k * ‖f ξ‖) volume) :
    ContDiff ℝ ∞ (fun x : Space => inverseL1Representative f hf x) :=
  contDiff_inverseL1Representative f hf hm

end R3EhrenfestFourierL1L2.ExpectedTypes

-- Exact named reports are executed only by authorized cached external CI.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative"
#check @MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative"
#print axioms MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_apply"
#check @MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_apply
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_apply"
#print axioms MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.continuous_fourierInv_integral"
#check @MethbokeAddon.R3Ehrenfest.FourierL1L2.continuous_fourierInv_integral
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.continuous_fourierInv_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.continuous_fourierInv_integral"
#print axioms MethbokeAddon.R3Ehrenfest.FourierL1L2.continuous_fourierInv_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.continuous_fourierInv_integral"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.fourierInv_integral_ae"
#check @MethbokeAddon.R3Ehrenfest.FourierL1L2.fourierInv_integral_ae
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.fourierInv_integral_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.fourierInv_integral_ae"
#print axioms MethbokeAddon.R3Ehrenfest.FourierL1L2.fourierInv_integral_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.fourierInv_integral_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_ae"
#check @MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_ae
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_ae"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_ae"
#print axioms MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_ae
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.inverseL1Representative_ae"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.norm_inverseL1Representative_le"
#check @MethbokeAddon.R3Ehrenfest.FourierL1L2.norm_inverseL1Representative_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.norm_inverseL1Representative_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.norm_inverseL1Representative_le"
#print axioms MethbokeAddon.R3Ehrenfest.FourierL1L2.norm_inverseL1Representative_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.norm_inverseL1Representative_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.contDiff_inverseL1Representative"
#check @MethbokeAddon.R3Ehrenfest.FourierL1L2.contDiff_inverseL1Representative
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.contDiff_inverseL1Representative"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.FourierL1L2.contDiff_inverseL1Representative"
#print axioms MethbokeAddon.R3Ehrenfest.FourierL1L2.contDiff_inverseL1Representative
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.FourierL1L2.contDiff_inverseL1Representative"

