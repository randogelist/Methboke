import FDSNResidualAdmission.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open Set SingularClosure
open MethbokeAddon.EhrenfestObstruction MethbokeAddon.WeakFouriermanB
open MethbokeAddon.FeffermanFamily
open scoped BigOperators ContDiff Topology

/- residual_local_laplacian_contDiffOn. -/
example (h : Velocity) (T : ℝ)
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2) (localFrontSpacetime T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => laplacian (h z.1) z.2)
      (localFrontSpacetime T) :=
  MethbokeAddon.FDSN.residual_local_laplacian_contDiffOn h T hh

/- residual_local_transport_contDiffOn. -/
example (a b : Velocity) (T : ℝ)
    (ha : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => a z.1 z.2) (localFrontSpacetime T))
    (hb : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => b z.1 z.2) (localFrontSpacetime T)) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => fderiv ℝ (b z.1) z.2 (a z.1 z.2))
      (localFrontSpacetime T) :=
  MethbokeAddon.FDSN.residual_local_transport_contDiffOn a b T ha hb

/- residualForce_contDiffOn_front: actual residual expanded. -/
example (ν : ℝ) (U F h : Velocity) (T : ℝ)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) (localFrontSpacetime T))
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2) (localFrontSpacetime T)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      F z.1 z.2 + timeDerivative h z.1 z.2 - ν • laplacian (h z.1) z.2 +
        physicalTransport (U z.1) (h z.1) z.2 +
        physicalTransport (h z.1) (U z.1) z.2 + convection (h z.1) z.2)
      (localFrontSpacetime T) :=
  MethbokeAddon.FDSN.residualForce_contDiffOn_front ν U F h T hU hF hh

/- residualForce_contDiff_of_timeSupport_inside: global smoothness payload. -/
example (ν : ℝ) (U F h : Velocity) (T : ℝ)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hF : ContDiff ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2))
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2) (localFrontSpacetime T))
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec =>
      F z.1 z.2 + timeDerivative h z.1 z.2 - ν • laplacian (h z.1) z.2 +
        physicalTransport (U z.1) (h z.1) z.2 +
        physicalTransport (h z.1) (U z.1) z.2 + convection (h z.1) z.2) :=
  MethbokeAddon.FDSN.residualForce_contDiff_of_timeSupport_inside ν U F h T hU hF hh hsupp

/- residual_transport_spatialPeriodic: literal transport. -/
example (a b : Field) (ha : SpatialPeriodic a) (hb : SpatialPeriodic b) :
    SpatialPeriodic (fun x : Vec => fderiv ℝ b x (a x)) :=
  MethbokeAddon.FDSN.residual_transport_spatialPeriodic a b ha hb

/- residualForce_spatialPeriodic_of_timeSupport_inside. -/
example (ν : ℝ) (U F h : Velocity) (T : ℝ)
    (hU : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (U t))
    (hF : ∀ t : ℝ, SpatialPeriodic (F t))
    (hh : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (h t))
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T) :
    ∀ t : ℝ, SpatialPeriodic (fun x : Vec =>
      F t x + timeDerivative h t x - ν • laplacian (h t) x +
        physicalTransport (U t) (h t) x +
        physicalTransport (h t) (U t) x + convection (h t) x) :=
  MethbokeAddon.FDSN.residualForce_spatialPeriodic_of_timeSupport_inside ν U F h T hU hF hh hsupp

/- compact_timeSupport_positive_interval. -/
example (h : Velocity) (T : ℝ) (hh : HasCompactSupport h)
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport h ⊆ Icc a b :=
  MethbokeAddon.FDSN.compact_timeSupport_positive_interval h T hh hsupp

/- admissiblePeriodicForce_residual: exact original record endpoint. -/
example (ν : ℝ) (U F h : Velocity) (T : ℝ)
    (hF : AdmissiblePeriodicForce F)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2) (localFrontSpacetime T))
    (hUp : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (U t))
    (hhp : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (h t))
    (hhcompact : HasCompactSupport h)
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T) :
    AdmissiblePeriodicForce (MethbokeAddon.FDSN.residualForce ν U F h) :=
  MethbokeAddon.FDSN.admissiblePeriodicForce_residual ν U F h T
    hF hU hh hUp hhp hhcompact hsupp

/- Independent literal projection of all three admission fields. -/
example (ν : ℝ) (U F h : Velocity) (T : ℝ)
    (hF : AdmissiblePeriodicForce F)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hh : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => h z.1 z.2) (localFrontSpacetime T))
    (hUp : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (U t))
    (hhp : ∀ t ∈ Ioo (0 : ℝ) T, SpatialPeriodic (h t))
    (hhcompact : HasCompactSupport h)
    (hsupp : tsupport h ⊆ Ioo (0 : ℝ) T) :
    ContDiff ℝ ∞ (fun z : ℝ × Vec => MethbokeAddon.FDSN.residualForce ν U F h z.1 z.2) ∧
    (∀ t : ℝ, SpatialPeriodic (MethbokeAddon.FDSN.residualForce ν U F h t)) ∧
    (∃ a b : ℝ, 0 < a ∧ a < b ∧
      ∀ t : ℝ, t ∉ Icc a b → MethbokeAddon.FDSN.residualForce ν U F h t = 0) := by
  have H := MethbokeAddon.FDSN.admissiblePeriodicForce_residual ν U F h T
    hF hU hh hUp hhp hhcompact hsupp
  exact ⟨H.smooth, H.periodic, H.time_support⟩


#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residual_local_laplacian_contDiffOn"
#check @MethbokeAddon.FDSN.residual_local_laplacian_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residual_local_laplacian_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residual_local_laplacian_contDiffOn"
#print axioms MethbokeAddon.FDSN.residual_local_laplacian_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residual_local_laplacian_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residual_local_transport_contDiffOn"
#check @MethbokeAddon.FDSN.residual_local_transport_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residual_local_transport_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residual_local_transport_contDiffOn"
#print axioms MethbokeAddon.FDSN.residual_local_transport_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residual_local_transport_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce_contDiffOn_front"
#check @MethbokeAddon.FDSN.residualForce_contDiffOn_front
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce_contDiffOn_front"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce_contDiffOn_front"
#print axioms MethbokeAddon.FDSN.residualForce_contDiffOn_front
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce_contDiffOn_front"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce_contDiff_of_timeSupport_inside"
#check @MethbokeAddon.FDSN.residualForce_contDiff_of_timeSupport_inside
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce_contDiff_of_timeSupport_inside"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce_contDiff_of_timeSupport_inside"
#print axioms MethbokeAddon.FDSN.residualForce_contDiff_of_timeSupport_inside
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce_contDiff_of_timeSupport_inside"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residual_transport_spatialPeriodic"
#check @MethbokeAddon.FDSN.residual_transport_spatialPeriodic
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residual_transport_spatialPeriodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residual_transport_spatialPeriodic"
#print axioms MethbokeAddon.FDSN.residual_transport_spatialPeriodic
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residual_transport_spatialPeriodic"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce_spatialPeriodic_of_timeSupport_inside"
#check @MethbokeAddon.FDSN.residualForce_spatialPeriodic_of_timeSupport_inside
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce_spatialPeriodic_of_timeSupport_inside"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce_spatialPeriodic_of_timeSupport_inside"
#print axioms MethbokeAddon.FDSN.residualForce_spatialPeriodic_of_timeSupport_inside
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce_spatialPeriodic_of_timeSupport_inside"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.compact_timeSupport_positive_interval"
#check @MethbokeAddon.FDSN.compact_timeSupport_positive_interval
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.compact_timeSupport_positive_interval"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.compact_timeSupport_positive_interval"
#print axioms MethbokeAddon.FDSN.compact_timeSupport_positive_interval
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.compact_timeSupport_positive_interval"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.admissiblePeriodicForce_residual"
#check @MethbokeAddon.FDSN.admissiblePeriodicForce_residual
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.admissiblePeriodicForce_residual"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.admissiblePeriodicForce_residual"
#print axioms MethbokeAddon.FDSN.admissiblePeriodicForce_residual
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.admissiblePeriodicForce_residual"

