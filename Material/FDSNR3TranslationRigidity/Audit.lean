import FDSNR3TranslationRigidity.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set SingularClosure Metric MethbokeAddon.FDSNR3
open scoped ContDiff FourierTransform

example (c y : Vec) {r : ℝ} (hr : 0 < r)
    (hphase : ∀ ξ ∈ Metric.ball c r,
      MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y ξ) = 1) : y = 0 :=
  translation_eq_zero_of_phase_one_on_ball c y hr hphase

example {β : ℝ → ℝ} {ψ : Vec → ℝ} {t : ℝ} (hβ : β t = 1)
    (c : Vec → ℂ) (active anchor : Vec) {r : ℝ} (hr : 0 < r)
    (hactive : ψ active = 1) (hcactive : c active ≠ 0)
    (hanchor : ∀ ξ ∈ Metric.ball anchor r, ψ ξ = 0 ∧ c ξ ≠ 0)
    {lam eta : ℝ} (hlam : |lam| < Real.pi / 4)
    (heta : |eta| < Real.pi / 4) (hne : lam ≠ eta) (y : Vec) :
    ¬ ∀ ξ : Vec, packetRotate β ψ lam t c ξ =
      MethbokeAddon.FDSN.phase (2 * Real.pi * inner ℝ y ξ) *
        packetRotate β ψ eta t c ξ :=
  packet_phase_not_translation hβ c active anchor hr hactive hcactive hanchor
    hlam heta hne y

example (U : ℝ → Velocity) (β : ℝ → ℝ) (ψ : Vec → ℝ)
    (c : Vec → CVec) (tstar : ℝ) (hβ : β tstar = 1)
    (i : Fin 3) (active anchor : Vec) {r : ℝ} (hr : 0 < r)
    (hactive : ψ active = 1) (hcactive : c active i ≠ 0)
    (hanchor : ∀ ξ ∈ Metric.ball anchor r, ψ ξ = 0 ∧ c ξ i ≠ 0)
    (hFourier : ∀ lam : ℝ, |lam| < Real.pi / 4 → ∀ ξ : Vec,
      fourierVelocity (U lam tstar) ξ = packetRotate β ψ lam tstar c ξ) :
    TranslationSeparation tstar (Real.pi / 4) U :=
  translationSeparation_of_actual_packet_fourier U β ψ c tstar hβ i
    active anchor hr hactive hcactive hanchor hFourier

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.translation_eq_zero_of_phase_one_on_ball"
#check @MethbokeAddon.FDSNR3.translation_eq_zero_of_phase_one_on_ball
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.translation_eq_zero_of_phase_one_on_ball"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.translation_eq_zero_of_phase_one_on_ball"
#print axioms MethbokeAddon.FDSNR3.translation_eq_zero_of_phase_one_on_ball
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.translation_eq_zero_of_phase_one_on_ball"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packet_phase_not_translation"
#check @MethbokeAddon.FDSNR3.packet_phase_not_translation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packet_phase_not_translation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packet_phase_not_translation"
#print axioms MethbokeAddon.FDSNR3.packet_phase_not_translation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packet_phase_not_translation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.translationSeparation_of_actual_packet_fourier"
#check @MethbokeAddon.FDSNR3.translationSeparation_of_actual_packet_fourier
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.translationSeparation_of_actual_packet_fourier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.translationSeparation_of_actual_packet_fourier"
#print axioms MethbokeAddon.FDSNR3.translationSeparation_of_actual_packet_fourier
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.translationSeparation_of_actual_packet_fourier"

