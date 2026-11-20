import FDSNJointResidual.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false

noncomputable section

open Set Filter SingularClosure
open MethbokeAddon.EhrenfestObstruction MethbokeAddon.WeakFouriermanB
open MethbokeAddon.FDSN
open scoped BigOperators ContDiff Topology

example
    (H : ℝ → Velocity) (q : ℝ × (ℝ × Vec))
    (hH : ContDiffAt ℝ ∞ (fun z : ℝ × (ℝ × Vec) => H z.1 z.2.1 z.2.2) q) :
    ContDiffAt ℝ ∞ (fun z : ℝ × (ℝ × Vec) =>
      fderiv ℝ (H z.1 z.2.1) z.2.2) q :=
  family_spatial_fderiv_contDiffAt H q hH

example
    (H : ℝ → Velocity) (T : ℝ)
    (hH : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => H q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T}) (j : Fin 3) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      coordinateDerivative (H q.1 q.2.1) j q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} :=
  family_coordinateDerivative_contDiffOn H T hH j

example
    (H : ℝ → Velocity) (T : ℝ)
    (hH : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => H q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T}) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => laplacian (H q.1 q.2.1) q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} :=
  family_laplacian_contDiffOn H T hH

example
    (A B : ℝ → Velocity) (T : ℝ)
    (hA : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => A q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T})
    (hB : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => B q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T}) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      physicalTransport (A q.1 q.2.1) (B q.1 q.2.1) q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} :=
  family_transport_contDiffOn A B T hA hB

example
    (H : ℝ → Velocity) (T : ℝ)
    (hH : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => H q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T}) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => timeDerivative (H q.1) q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} :=
  family_timeDerivative_contDiffOn H T hH

example
    (ν : ℝ) (U F : Velocity) (H : ℝ → Velocity) (T : ℝ)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hF : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) (localFrontSpacetime T))
    (hH : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => H q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T}) :
    ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      F q.2.1 q.2.2 + timeDerivative (H q.1) q.2.1 q.2.2
        - ν • laplacian (H q.1 q.2.1) q.2.2
        + physicalTransport (U q.2.1) (H q.1 q.2.1) q.2.2
        + physicalTransport (H q.1 q.2.1) (U q.2.1) q.2.2
        + convection (H q.1 q.2.1) q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T} :=
  residualForce_joint_contDiffOn_front ν U F H T hU hF hH

example
    (ν : ℝ) (U F : Velocity) (H : ℝ → Velocity) (T : ℝ)
    (hU : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U z.1 z.2) (localFrontSpacetime T))
    (hF : ContDiff ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2))
    (hH : ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) => H q.1 q.2.1 q.2.2)
      {q | q.2.1 ∈ Ioo (0 : ℝ) T})
    (S : Set ℝ) (hS : IsClosed S) (hST : S ⊆ Ioo (0 : ℝ) T)
    (hsupp : ∀ lambda : ℝ, tsupport (H lambda) ⊆ S) :
    ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      F q.2.1 q.2.2 + timeDerivative (H q.1) q.2.1 q.2.2
        - ν • laplacian (H q.1 q.2.1) q.2.2
        + physicalTransport (U q.2.1) (H q.1 q.2.1) q.2.2
        + physicalTransport (H q.1 q.2.1) (U q.2.1) q.2.2
        + convection (H q.1 q.2.1) q.2.2) :=
  residualForce_joint_contDiff_of_common_timeSupport ν U F H T hU hF hH S hS hST hsupp

example (ν : ℝ) (U F : Velocity) :
    residualForce ν U F 0 = F :=
  residualForce_zero_correction ν U F


#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.family_spatial_fderiv_contDiffAt"
#check @MethbokeAddon.FDSN.family_spatial_fderiv_contDiffAt
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.family_spatial_fderiv_contDiffAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.family_spatial_fderiv_contDiffAt"
#print axioms MethbokeAddon.FDSN.family_spatial_fderiv_contDiffAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.family_spatial_fderiv_contDiffAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.family_coordinateDerivative_contDiffOn"
#check @MethbokeAddon.FDSN.family_coordinateDerivative_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.family_coordinateDerivative_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.family_coordinateDerivative_contDiffOn"
#print axioms MethbokeAddon.FDSN.family_coordinateDerivative_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.family_coordinateDerivative_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.family_laplacian_contDiffOn"
#check @MethbokeAddon.FDSN.family_laplacian_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.family_laplacian_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.family_laplacian_contDiffOn"
#print axioms MethbokeAddon.FDSN.family_laplacian_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.family_laplacian_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.family_transport_contDiffOn"
#check @MethbokeAddon.FDSN.family_transport_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.family_transport_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.family_transport_contDiffOn"
#print axioms MethbokeAddon.FDSN.family_transport_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.family_transport_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.family_timeDerivative_contDiffOn"
#check @MethbokeAddon.FDSN.family_timeDerivative_contDiffOn
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.family_timeDerivative_contDiffOn"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.family_timeDerivative_contDiffOn"
#print axioms MethbokeAddon.FDSN.family_timeDerivative_contDiffOn
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.family_timeDerivative_contDiffOn"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce_joint_contDiffOn_front"
#check @MethbokeAddon.FDSN.residualForce_joint_contDiffOn_front
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce_joint_contDiffOn_front"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce_joint_contDiffOn_front"
#print axioms MethbokeAddon.FDSN.residualForce_joint_contDiffOn_front
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce_joint_contDiffOn_front"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce_joint_contDiff_of_common_timeSupport"
#check @MethbokeAddon.FDSN.residualForce_joint_contDiff_of_common_timeSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce_joint_contDiff_of_common_timeSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce_joint_contDiff_of_common_timeSupport"
#print axioms MethbokeAddon.FDSN.residualForce_joint_contDiff_of_common_timeSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce_joint_contDiff_of_common_timeSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.residualForce_zero_correction"
#check @MethbokeAddon.FDSN.residualForce_zero_correction
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.residualForce_zero_correction"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.residualForce_zero_correction"
#print axioms MethbokeAddon.FDSN.residualForce_zero_correction
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.residualForce_zero_correction"

