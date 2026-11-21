import R3EhrenfestCarrier.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory FourierTransform
open scoped FourierTransform

namespace R3EhrenfestCarrier.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.LerayMultiplier
open MethbokeAddon.R3Ehrenfest.SharpCutoff
open MethbokeAddon.R3Ehrenfest.Carrier
open QFA.Endpoints.Agmon (ComplexL2)
open QFA.Endpoints.Representation

-- The actual full-space L2 carrier and the literal two fixed-point equations.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example (n : ℕ) : ClosedSubmodule ℝ SpatialL2 := bandlimitedSolenoidalGraph n
example (n : ℕ) (v : SpatialL2) :
    v ∈ bandlimitedSolenoidalGraph n ↔ sharpCutoff n v = v ∧ realLeray v = v :=
  mem_bandlimitedSolenoidalGraph_iff n v
example (n : ℕ) :
    BandlimitedSolenoidal n = (bandlimitedSolenoidalGraph n).toSubmodule := rfl
example (n : ℕ) : CompleteSpace (BandlimitedSolenoidal n) :=
  bandlimitedSolenoidalCompleteSpace n
example (n : ℕ) : IsClosed (bandlimitedSolenoidalGraph n : Set SpatialL2) :=
  bandlimitedSolenoidal_isClosed n

example (n : ℕ) : BandlimitedSolenoidal n →L[ℝ] SpatialL2 := bandlimitedInclusionCLM n
example (n : ℕ) (v : BandlimitedSolenoidal n) :
    bandlimitedInclusionCLM n v = (v : SpatialL2) := bandlimitedInclusionCLM_apply n v
example (n : ℕ) (v : BandlimitedSolenoidal n) :
    sharpCutoff n (v : SpatialL2) = (v : SpatialL2) := sharpCutoff_coe n v
example (n : ℕ) (v : BandlimitedSolenoidal n) :
    realLeray (v : SpatialL2) = (v : SpatialL2) := realLeray_coe n v
example (n : ℕ) (v : BandlimitedSolenoidal n) :
    Solenoidal (v : SpatialL2) := solenoidal_coe n v

-- There is no finite-dimensionality or supplied projection premise.
example (n : ℕ) (v : SpatialL2) :
    sharpCutoff n (realLeray v) ∈ bandlimitedSolenoidalGraph n :=
  sharpCutoff_realLeray_mem n v
example (n : ℕ) : SpatialL2 →L[ℝ] BandlimitedSolenoidal n := bandlimitedProject n
example (n : ℕ) (v : SpatialL2) :
    (bandlimitedProject n v : SpatialL2) = sharpCutoff n (realLeray v) :=
  bandlimitedProject_coe n v
example (n : ℕ) (v : SpatialL2) :
    ‖bandlimitedProject n v‖ ≤ ‖v‖ := norm_bandlimitedProject_le n v
example (n : ℕ) (v : BandlimitedSolenoidal n) :
    bandlimitedProject n (v : SpatialL2) = v := bandlimitedProject_inclusion n v
example (n : ℕ) : Function.Surjective (bandlimitedProject n) := bandlimitedProject_surjective n
example (n : ℕ) (u v : SpatialL2) :
    inner ℝ (bandlimitedProject n u : SpatialL2) v =
      inner ℝ u (bandlimitedProject n v : SpatialL2) :=
  inner_bandlimitedProject_left n u v
example (n : ℕ) (v : BandlimitedSolenoidal n) :
    ∀ᵐ ξ : Space ∂volume, (n : ℝ) + 1 < ‖ξ‖ →
      (𝓕 (complexifyL2 (v : SpatialL2)) : ComplexL2) ξ = 0 :=
  bandlimitedSolenoidal_fourier_outside n v

end R3EhrenfestCarrier.ExpectedTypes

-- Ordered exact-type and named axiom reports, executed only by authorized external CI.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalGraph"
#check @MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalGraph
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalGraph"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalGraph"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalGraph
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalGraph"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.mem_bandlimitedSolenoidalGraph_iff"
#check @MethbokeAddon.R3Ehrenfest.Carrier.mem_bandlimitedSolenoidalGraph_iff
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.mem_bandlimitedSolenoidalGraph_iff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.mem_bandlimitedSolenoidalGraph_iff"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.mem_bandlimitedSolenoidalGraph_iff
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.mem_bandlimitedSolenoidalGraph_iff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.BandlimitedSolenoidal"
#check @MethbokeAddon.R3Ehrenfest.Carrier.BandlimitedSolenoidal
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.BandlimitedSolenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.BandlimitedSolenoidal"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.BandlimitedSolenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.BandlimitedSolenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalCompleteSpace"
#check @MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalCompleteSpace
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalCompleteSpace"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalCompleteSpace"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalCompleteSpace
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidalCompleteSpace"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_isClosed"
#check @MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_isClosed
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_isClosed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_isClosed"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_isClosed
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_isClosed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM"
#check @MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM_apply"
#check @MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM_apply"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedInclusionCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_coe"
#check @MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_coe
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_coe"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_coe"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_coe
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_coe"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.realLeray_coe"
#check @MethbokeAddon.R3Ehrenfest.Carrier.realLeray_coe
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.realLeray_coe"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.realLeray_coe"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.realLeray_coe
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.realLeray_coe"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.solenoidal_coe"
#check @MethbokeAddon.R3Ehrenfest.Carrier.solenoidal_coe
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.solenoidal_coe"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.solenoidal_coe"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.solenoidal_coe
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.solenoidal_coe"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_realLeray_mem"
#check @MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_realLeray_mem
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_realLeray_mem"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_realLeray_mem"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_realLeray_mem
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.sharpCutoff_realLeray_mem"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject"
#check @MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_coe"
#check @MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_coe
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_coe"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_coe"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_coe
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_coe"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.norm_bandlimitedProject_le"
#check @MethbokeAddon.R3Ehrenfest.Carrier.norm_bandlimitedProject_le
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.norm_bandlimitedProject_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.norm_bandlimitedProject_le"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.norm_bandlimitedProject_le
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.norm_bandlimitedProject_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_inclusion"
#check @MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_inclusion
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_inclusion"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_inclusion"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_inclusion
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_inclusion"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_surjective"
#check @MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_surjective
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_surjective"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_surjective"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_surjective
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedProject_surjective"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.inner_bandlimitedProject_left"
#check @MethbokeAddon.R3Ehrenfest.Carrier.inner_bandlimitedProject_left
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.inner_bandlimitedProject_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.inner_bandlimitedProject_left"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.inner_bandlimitedProject_left
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.inner_bandlimitedProject_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_fourier_outside"
#check @MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_fourier_outside
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_fourier_outside"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_fourier_outside"
#print axioms MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_fourier_outside
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.Carrier.bandlimitedSolenoidal_fourier_outside"

