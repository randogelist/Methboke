import EhrenfestCrossTransport.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independent exact consumer types; external evidence pending. -/

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff RealInnerProductSpace
open MethbokeAddon.EhrenfestObstruction

example (a b : Field) (ha : Continuous a) (hb : ContDiff ℝ ∞ b) :
    Continuous (physicalTransport a b) :=
  physicalTransport_continuous a b ha hb

example (a b : Field) (x : Vec) :
    ‖physicalTransport a b x‖ ≤ ‖fderiv ℝ b x‖ * ‖a x‖ :=
  physicalTransport_norm_le a b x

example (w v : Field) (hw : ContDiff ℝ ∞ w) (hv : ContDiff ℝ ∞ v) :
    convection (w + v) =
      convection w + physicalTransport v w + physicalTransport w v + convection v :=
  convection_add_eq_transport w v hw hv

example (U v : Field) (hU : ContDiff ℝ ∞ U) (hv : ContDiff ℝ ∞ v) :
    physicalReferenceResidual U v (U - v) = convection U - convection v :=
  physicalReferenceResidual_eq_convection_sub U v hU hv

example (U v r : Field)
    (hU : ContDiff ℝ ∞ U) (hv : Continuous v) (hr : ContDiff ℝ ∞ r) :
    Continuous (physicalReferenceResidual U v r) :=
  physicalReferenceResidual_continuous U v r hU hv hr

example (a b : Vec) : ‖a + b‖ ^ 2 ≤ 2 * (‖a‖ ^ 2 + ‖b‖ ^ 2) :=
  norm_add_sq_le_two a b

example (M : ℝ) (hM : 0 ≤ M) (U v r : Field) (x : Vec)
    (hDU : ‖fderiv ℝ U x‖ ≤ M) (hv : ‖v x‖ ≤ M) :
    ‖physicalReferenceResidual U v r x‖ ^ 2 ≤
      (2 * M ^ 2) * ‖r x‖ ^ 2 +
        (6 * M ^ 2) * gradientSquareDensity r x :=
  physicalReferenceResidual_norm_sq_le M hM U v r x hDU hv

example (M : ℝ) (hM : 0 ≤ M) (U v r : Field)
    (hU : ContDiff ℝ ∞ U) (hv : Continuous v) (hr : ContDiff ℝ ∞ r)
    (hDUM : ∀ x ∈ unitCube, ‖fderiv ℝ U x‖ ≤ M)
    (hvM : ∀ x ∈ unitCube, ‖v x‖ ≤ M) :
    (∫ x in unitCube, ‖physicalReferenceResidual U v r x‖ ^ 2) ≤
      (6 * M ^ 2) * ((∫ x in unitCube, ‖r x‖ ^ 2) + physicalDissipation r) :=
  physicalReferenceResidual_l2_le M hM U v r hU hv hr hDUM hvM

example (a b c : Vec) :
    ‖a - b - c‖ ^ 2 ≤ 3 * (‖a‖ ^ 2 + ‖b‖ ^ 2 + ‖c‖ ^ 2) :=
  norm_sub_sub_sq_le_three a b c

example (v w R : Field)
    (hv : ContDiff ℝ ∞ v) (hw : ContDiff ℝ ∞ w) (hR : Continuous R) :
    Continuous (physicalErrorForcing v w R) :=
  physicalErrorForcing_continuous v w R hv hw hR

example (M : ℝ) (hM : 0 ≤ M) (v w R : Field) (x : Vec)
    (hv : ‖v x‖ ≤ M) (hDv : ‖fderiv ℝ v x‖ ≤ M) :
    ‖physicalErrorForcing v w R x‖ ^ 2 ≤
      3 * ‖R x‖ ^ 2 + (9 * M ^ 2) * gradientSquareDensity w x +
        (3 * M ^ 2) * ‖w x‖ ^ 2 :=
  physicalErrorForcing_norm_sq_le M hM v w R x hv hDv

example (M : ℝ) (hM : 0 ≤ M) (N : ℕ) (c : FourierCoeff)
    (hreal : SpectralReality c) (v R : Field)
    (hv : ContDiff ℝ ∞ v) (hR : Continuous R)
    (hvM : ∀ x ∈ unitCube, ‖v x‖ ≤ M)
    (hDvM : ∀ x ∈ unitCube, ‖fderiv ℝ v x‖ ≤ M) :
    (∫ x in unitCube, ‖physicalErrorForcing v (finiteSynthesis N c) R x‖ ^ 2) ≤
      3 * (∫ x in unitCube, ‖R x‖ ^ 2) +
        (12 * M ^ 2) * coefficientDissipation N c :=
  finite_physicalErrorForcing_l2_le M hM N c hreal v R hv hR hvM hDvM

example :
    ∃ C : ℝ, 0 < C ∧ ∀ ν : ℝ, 0 < ν → ∀ M : ℝ, 0 ≤ M →
      ∀ N : ℕ, ∀ c : ℝ → FourierCoeff, ∀ v R : Field,
      ContDiff ℝ ∞ v → Continuous R →
      (∀ x ∈ unitCube, ‖v x‖ ≤ M) →
      (∀ x ∈ unitCube, ‖fderiv ℝ v x‖ ≤ M) →
      ∀ s : Set ℝ, ∀ t : ℝ,
      (∀ k : Frequency, k ∉ cutoffModes N → ∀ i : Fin 3, c t k i = 0) →
      SpectralReality (c t) → SpectralSolenoidal (c t) →
      (∀ k ∈ cutoffModes N, ∀ i : Fin 3,
        HasDerivWithinAt (fun r => c r k i)
          (galerkinRhs ν N (c t) k i +
            cutoffCoeff N (fun l => coefficientLeray l
              (datumFourierCoeff
                (physicalErrorForcing v (finiteSynthesis N (c t)) R) l)) k i) s t) →
      ∃ d : ℝ,
        HasDerivWithinAt (fun r => coefficientDissipation N (c r)) d s t ∧
        d ≤ C / ν ^ 3 * (coefficientDissipation N (c t)) ^ 3 +
          (24 * M ^ 2 / ν) * coefficientDissipation N (c t) +
            (6 / ν) * (∫ x in unitCube, ‖R x‖ ^ 2) :=
  FINITE_ERROR_CROSS_ENSTROPHY_INEQUALITY


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalTransport_continuous"
#check @MethbokeAddon.EhrenfestObstruction.physicalTransport_continuous
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalTransport_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalTransport_continuous"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalTransport_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalTransport_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalTransport_norm_le"
#check @MethbokeAddon.EhrenfestObstruction.physicalTransport_norm_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalTransport_norm_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalTransport_norm_le"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalTransport_norm_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalTransport_norm_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.convection_add_eq_transport"
#check @MethbokeAddon.EhrenfestObstruction.convection_add_eq_transport
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.convection_add_eq_transport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.convection_add_eq_transport"
#print axioms MethbokeAddon.EhrenfestObstruction.convection_add_eq_transport
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.convection_add_eq_transport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_eq_convection_sub"
#check @MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_eq_convection_sub
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_eq_convection_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_eq_convection_sub"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_eq_convection_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_eq_convection_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_continuous"
#check @MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_continuous
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_continuous"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.norm_add_sq_le_two"
#check @MethbokeAddon.EhrenfestObstruction.norm_add_sq_le_two
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.norm_add_sq_le_two"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.norm_add_sq_le_two"
#print axioms MethbokeAddon.EhrenfestObstruction.norm_add_sq_le_two
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.norm_add_sq_le_two"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_norm_sq_le"
#check @MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_norm_sq_le"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_l2_le"
#check @MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_l2_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_l2_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_l2_le"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_l2_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalReferenceResidual_l2_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.norm_sub_sub_sq_le_three"
#check @MethbokeAddon.EhrenfestObstruction.norm_sub_sub_sq_le_three
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.norm_sub_sub_sq_le_three"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.norm_sub_sub_sq_le_three"
#print axioms MethbokeAddon.EhrenfestObstruction.norm_sub_sub_sq_le_three
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.norm_sub_sub_sq_le_three"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_continuous"
#check @MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_continuous
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_continuous"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_continuous"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_continuous
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_continuous"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_norm_sq_le"
#check @MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_norm_sq_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_norm_sq_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_norm_sq_le"
#print axioms MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_norm_sq_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.physicalErrorForcing_norm_sq_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.finite_physicalErrorForcing_l2_le"
#check @MethbokeAddon.EhrenfestObstruction.finite_physicalErrorForcing_l2_le
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.finite_physicalErrorForcing_l2_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.finite_physicalErrorForcing_l2_le"
#print axioms MethbokeAddon.EhrenfestObstruction.finite_physicalErrorForcing_l2_le
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.finite_physicalErrorForcing_l2_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_CROSS_ENSTROPHY_INEQUALITY"
#check @MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_CROSS_ENSTROPHY_INEQUALITY
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_CROSS_ENSTROPHY_INEQUALITY"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_CROSS_ENSTROPHY_INEQUALITY"
#print axioms MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_CROSS_ENSTROPHY_INEQUALITY
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.FINITE_ERROR_CROSS_ENSTROPHY_INEQUALITY"

