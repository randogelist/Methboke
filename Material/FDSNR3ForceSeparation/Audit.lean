import FDSNR3ForceSeparation.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section
open Set Filter MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open MethbokeAddon.EhrenfestObstruction
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology

example : ∀ (f : 𝓢(Vec, Vec)) (hf : ∀ x : Vec, divergence (f : Field) x = 0),
    physicalLeray (f : Field) = (f : Field) :=
  @physicalLeray_eq_of_divergence_free_schwartz

example : ∀ (c : ℝ) (f : 𝓢(Vec, Vec))
    (hf : ∀ x : Vec, divergence (f : Field) x = 0),
    ∀ x : Vec, divergence (c • f : 𝓢(Vec, Vec)) x = 0 :=
  @divergence_free_schwartz_const_smul

example : ∀ (c : ℝ) (f : 𝓢(Vec, Vec))
    (hf : ∀ x : Vec, divergence (f : Field) x = 0),
    physicalLeray (c • (f : Field)) = c • (f : Field) :=
  @physicalLeray_const_smul_solenoidal_schwartz

example : ∀ (ν : ℝ) (U F h : Velocity) (t : ℝ) (hz : h t = 0),
    MethbokeAddon.FDSN.residualForce ν U F h t = F t + timeDerivative h t :=
  @residualForce_at_zero_slice

example : ∀ (ν : ℝ) (U F h k : Velocity) (t : ℝ)
    (hh : h t = 0) (hk : k t = 0),
    (MethbokeAddon.FDSN.residualForce ν U F h -
      MethbokeAddon.FDSN.residualForce ν U F k) t =
      timeDerivative h t - timeDerivative k t :=
  @residualForce_sub_at_common_zero

example : ∀ (ν : ℝ) (U F h k : Velocity) (t c : ℝ) (w : 𝓢(Vec, Vec))
    (hh : h t = 0) (hk : k t = 0)
    (hdt : timeDerivative h t - timeDerivative k t = c • (w : Field))
    (hw : ∀ x : Vec, divergence (w : Field) x = 0),
    physicalLeray ((MethbokeAddon.FDSN.residualForce ν U F h -
      MethbokeAddon.FDSN.residualForce ν U F k) t) = c • (w : Field) :=
  @physicalLeray_residual_difference_at_crossing

example : ∀ (ν : ℝ) (U F h k : Velocity) (t c : ℝ) (w : 𝓢(Vec, Vec))
    (hh : h t = 0) (hk : k t = 0)
    (hdt : timeDerivative h t - timeDerivative k t = c • (w : Field))
    (hwdiv : ∀ x : Vec, divergence (w : Field) x = 0)
    (hc : c ≠ 0) (hw : w ≠ 0),
    ∃ x : Vec, physicalLeray ((MethbokeAddon.FDSN.residualForce ν U F h -
      MethbokeAddon.FDSN.residualForce ν U F k) t) x ≠ 0 :=
  @projected_residual_difference_ne_zero_at_crossing

example : ∀ (ν T ε tzero slope : ℝ) (U F : Velocity) (h : ℝ → Velocity)
    (w : 𝓢(Vec, Vec)) (htzero : tzero ∈ Ico (0 : ℝ) T)
    (hslope : slope ≠ 0) (hw : w ≠ 0)
    (hwdiv : ∀ x : Vec, divergence (w : Field) x = 0)
    (hzero : ∀ lam : ℝ, |lam| < ε → h lam tzero = 0)
    (hdt : ∀ lam : ℝ, |lam| < ε →
      timeDerivative (h lam) tzero = (lam * slope) • (w : Field)),
    PhysicalProjectedForceSeparation T ε
      (fun lam => MethbokeAddon.FDSN.residualForce ν U F (h lam)) :=
  @physicalProjectedForceSeparation_of_common_crossing

example : ∀ (ν : ℝ) (U F h k : Velocity) (t c : ℝ)
    (ψ : Vec → ℝ) (hψ : ContDiff ℝ ∞ ψ) (hcψ : HasCompactSupport ψ)
    (ho : ∀ ξ : Vec, ψ (-ξ) = -ψ ξ)
    (f : 𝓢(Vec, Vec)) (hf : ∀ x : Vec, divergence (f : Field) x = 0)
    {ξ : Vec} {i : Fin 3} (hψξ : ψ ξ ≠ 0) (hfξ : fourierVelocity f ξ i ≠ 0)
    (hh : h t = 0) (hk : k t = 0) (hc : c ≠ 0)
    (hdt : timeDerivative h t - timeDerivative k t =
      c • (spectralGenerator ψ hψ hcψ f : Field)),
    ∃ x : Vec, physicalLeray ((MethbokeAddon.FDSN.residualForce ν U F h -
      MethbokeAddon.FDSN.residualForce ν U F k) t) x ≠ 0 :=
  @projected_residual_generator_difference_ne_zero

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalLeray_eq_of_divergence_free_schwartz"
#check @MethbokeAddon.FDSNR3.physicalLeray_eq_of_divergence_free_schwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalLeray_eq_of_divergence_free_schwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalLeray_eq_of_divergence_free_schwartz"
#print axioms MethbokeAddon.FDSNR3.physicalLeray_eq_of_divergence_free_schwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalLeray_eq_of_divergence_free_schwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.divergence_free_schwartz_const_smul"
#check @MethbokeAddon.FDSNR3.divergence_free_schwartz_const_smul
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.divergence_free_schwartz_const_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.divergence_free_schwartz_const_smul"
#print axioms MethbokeAddon.FDSNR3.divergence_free_schwartz_const_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.divergence_free_schwartz_const_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalLeray_const_smul_solenoidal_schwartz"
#check @MethbokeAddon.FDSNR3.physicalLeray_const_smul_solenoidal_schwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalLeray_const_smul_solenoidal_schwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalLeray_const_smul_solenoidal_schwartz"
#print axioms MethbokeAddon.FDSNR3.physicalLeray_const_smul_solenoidal_schwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalLeray_const_smul_solenoidal_schwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.residualForce_at_zero_slice"
#check @MethbokeAddon.FDSNR3.residualForce_at_zero_slice
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.residualForce_at_zero_slice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.residualForce_at_zero_slice"
#print axioms MethbokeAddon.FDSNR3.residualForce_at_zero_slice
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.residualForce_at_zero_slice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.residualForce_sub_at_common_zero"
#check @MethbokeAddon.FDSNR3.residualForce_sub_at_common_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.residualForce_sub_at_common_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.residualForce_sub_at_common_zero"
#print axioms MethbokeAddon.FDSNR3.residualForce_sub_at_common_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.residualForce_sub_at_common_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalLeray_residual_difference_at_crossing"
#check @MethbokeAddon.FDSNR3.physicalLeray_residual_difference_at_crossing
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalLeray_residual_difference_at_crossing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalLeray_residual_difference_at_crossing"
#print axioms MethbokeAddon.FDSNR3.physicalLeray_residual_difference_at_crossing
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalLeray_residual_difference_at_crossing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.projected_residual_difference_ne_zero_at_crossing"
#check @MethbokeAddon.FDSNR3.projected_residual_difference_ne_zero_at_crossing
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.projected_residual_difference_ne_zero_at_crossing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.projected_residual_difference_ne_zero_at_crossing"
#print axioms MethbokeAddon.FDSNR3.projected_residual_difference_ne_zero_at_crossing
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.projected_residual_difference_ne_zero_at_crossing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_of_common_crossing"
#check @MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_of_common_crossing
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_of_common_crossing"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_of_common_crossing"
#print axioms MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_of_common_crossing
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalProjectedForceSeparation_of_common_crossing"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.projected_residual_generator_difference_ne_zero"
#check @MethbokeAddon.FDSNR3.projected_residual_generator_difference_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.projected_residual_generator_difference_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.projected_residual_generator_difference_ne_zero"
#print axioms MethbokeAddon.FDSNR3.projected_residual_generator_difference_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.projected_residual_generator_difference_ne_zero"

