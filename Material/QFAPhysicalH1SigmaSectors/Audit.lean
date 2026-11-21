import QFAPhysicalH1SigmaSectors.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ContDiff

namespace QFAPhysicalH1SigmaSectors.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers
open MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers
open MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence
open MethbokeAddon.QuasiFeffermanA.SixSectorNaturality
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

-- Literal full-volume vector carriers and original compact-test predicates.
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : ComplexL2 = Lp (EuclideanSpace ℂ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example (v : SpatialL2) (G : Fin 3 → SpatialL2) : SpatialWeakGradient v G ↔
    ∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • v x) =
        -(∫ x : Space, ψ x • G j x) := Iff.rfl
example (v : SpatialL2) : Solenoidal v ↔
    ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun x : Space => inner ℝ (v x)
        (WithLp.toLp 2 (fun j : Fin 3 =>
          fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))))) volume ∧
        (∫ x : Space, inner ℝ (v x)
          (WithLp.toLp 2 (fun j : Fin 3 =>
            fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ))))) = 0 := Iff.rfl

-- Native Fourier naturality: arbitrary bounded complex-linear codomain map.
example (A : ComplexVector →L[ℂ] ComplexVector) (f : ComplexL2) :
    𝓕 (A.compLpL 2 volume f) = A.compLpL 2 volume (𝓕 f) := fourier_compLpL A f
example (i : Fin 6) (A : ComplexVector →L[ℂ] ComplexVector) (f : ComplexL2) :
    frequencySector i (A.compLpL 2 volume f) =
      A.compLpL 2 volume (frequencySector i f) := frequencySector_compLpL i A f
example (i : Fin 6) (A : ComplexVector →L[ℂ] ComplexVector) (f : ComplexL2) :
    fourierSector i (A.compLpL 2 volume f) =
      A.compLpL 2 volume (fourierSector i f) := fourierSector_compLpL i A f

-- The coordinate map is constructed by the literal first-coordinate slice.
example (j : Fin 3) : ComplexVector →L[ℂ] ComplexVector := complexCoordinateSliceVectorCLM j
example (j : Fin 3) : complexCoordinateSliceVectorCLM j =
    (PiLp.proj 2 (fun _ : Fin 3 => ℂ) j).smulRight
      (EuclideanSpace.single 0 (1 : ℂ)) := rfl
example (j : Fin 3) (z : ComplexVector) :
    complexCoordinateSliceVectorCLM j z = (z j) • EuclideanSpace.single 0 (1 : ℂ) :=
  complexCoordinateSliceVectorCLM_apply j z
example (j : Fin 3) (v : Space) :
    complexifyVectorLI (coordinateSliceVectorCLM j v) =
      complexCoordinateSliceVectorCLM j (complexifyVectorLI v) :=
  complexify_coordinateSliceVector j v
example (j : Fin 3) (u : SpatialL2) :
    complexifyL2 (coordinateSliceL2 j u) =
      (complexCoordinateSliceVectorCLM j).compLpL 2 volume (complexifyL2 u) :=
  complexify_coordinateSliceL2 j u
example (i : Fin 6) (j : Fin 3) (u : SpatialL2) :
    realFourierSector i (coordinateSliceL2 j u) =
      coordinateSliceL2 j (realFourierSector i u) := realFourierSector_coordinateSliceL2 i j u

-- Every term of the actual trace is transported, with no commutation premise.
example (i : Fin 6) (G : Fin 3 → SpatialL2) :
    (∑ j : Fin 3, coordinateSliceL2 j (realFourierSector i (G j))) =
      realFourierSector i (∑ j : Fin 3, coordinateSliceL2 j (G j)) :=
  spatialGradientTrace_realFourierSector i G

-- Complete physical derivative and solenoidal assumptions are the input only.
example (i : Fin 6) (v : SpatialL2) (G : Fin 3 → SpatialL2)
    (hweak : ∀ (j : Fin 3) (ψ : Space → ℝ),
      ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
        (∫ x : Space, fderiv ℝ ψ x (EuclideanSpace.single j (1 : ℝ)) • v x) =
          -(∫ x : Space, ψ x • G j x))
    (hsol : ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun x : Space => inner ℝ (v x) (scalarGradient ψ x)) volume ∧
        (∫ x : Space, inner ℝ (v x) (scalarGradient ψ x)) = 0) :
    ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun x : Space => inner ℝ (realFourierSector i v x)
        (scalarGradient ψ x)) volume ∧
        (∫ x : Space, inner ℝ (realFourierSector i v x) (scalarGradient ψ x)) = 0 :=
  solenoidal_realFourierSector i hweak hsol

-- The restricted carrier is the original graph, not an abstract projector record.
example : PhysicalH1Sigma = physicalH1SigmaGraph.toSubmodule := rfl
example (x : H1Ambient) : x ∈ physicalH1SigmaGraph ↔
    (∀ (j : Fin 3) (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      (∫ y : Space, fderiv ℝ ψ y (EuclideanSpace.single j (1 : ℝ)) • x 0 y) =
        -(∫ y : Space, ψ y • x j.succ y)) ∧
    (∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      Integrable (fun y : Space => inner ℝ (x 0 y) (scalarGradient ψ y)) volume ∧
        (∫ y : Space, inner ℝ (x 0 y) (scalarGradient ψ y)) = 0) :=
  mem_physicalH1SigmaGraph_iff x

example : PhysicalH1Sigma →ₗᵢ[ℝ] PhysicalH1 := physicalH1SigmaToH1LI
example (u : PhysicalH1Sigma) : (physicalH1SigmaToH1LI u).val = u.val :=
  physicalH1SigmaToH1LI_val u
example (u : PhysicalH1Sigma) :
    physicalH1Velocity (physicalH1SigmaToH1LI u) = u.val 0 := physicalH1SigmaToH1LI_velocity u
example (u : PhysicalH1Sigma) (j : Fin 3) :
    physicalH1Gradient j (physicalH1SigmaToH1LI u) = u.val j.succ :=
  physicalH1SigmaToH1LI_gradient u j

example (i : Fin 6) (u : PhysicalH1Sigma) : PhysicalH1Sigma := physicalH1SigmaSector i u
example (i : Fin 6) (u : PhysicalH1Sigma) :
    (physicalH1SigmaSector i u).val = WithLp.toLp 2
      (Fin.cons (realFourierSector i (u.val 0))
        (fun j => realFourierSector i (u.val j.succ))) := rfl
example (i : Fin 6) (u : PhysicalH1Sigma) :
    (physicalH1SigmaSector i u).val 0 = realFourierSector i (u.val 0) :=
  physicalH1SigmaSector_velocity i u
example (i : Fin 6) (u : PhysicalH1Sigma) (j : Fin 3) :
    (physicalH1SigmaSector i u).val j.succ = realFourierSector i (u.val j.succ) :=
  physicalH1SigmaSector_gradient i u j

-- Literal native solenoidal conclusion for the actual projected velocity.
example (i : Fin 6) (u : PhysicalH1Sigma) (ψ : Space → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hcompact : HasCompactSupport ψ) :
    Integrable (fun x : Space => inner ℝ (realFourierSector i (u.val 0) x)
      (scalarGradient ψ x)) volume ∧
      (∫ x : Space, inner ℝ (realFourierSector i (u.val 0) x) (scalarGradient ψ x)) = 0 :=
  physicalH1Sigma_solenoidal (physicalH1SigmaSector i u) ψ hψ hcompact

example (i : Fin 6) (u : PhysicalH1Sigma) :
    physicalH1SigmaToH1LI (physicalH1SigmaSector i u) =
      physicalH1Sector i (physicalH1SigmaToH1LI u) := physicalH1SigmaSector_toH1 i u
example (i : Fin 6) (u v : PhysicalH1Sigma) :
    physicalH1SigmaSector i (u + v) =
      physicalH1SigmaSector i u + physicalH1SigmaSector i v := physicalH1SigmaSector_add i u v
example (i : Fin 6) (r : ℝ) (u : PhysicalH1Sigma) :
    physicalH1SigmaSector i (r • u) = r • physicalH1SigmaSector i u :=
  physicalH1SigmaSector_smul i r u
example (i : Fin 6) : physicalH1SigmaSector i 0 = 0 := physicalH1SigmaSector_zero i
example (i : Fin 6) (u : PhysicalH1Sigma) : ‖physicalH1SigmaSector i u‖ ≤ ‖u‖ :=
  norm_physicalH1SigmaSector_le i u
example (i : Fin 6) : PhysicalH1Sigma →L[ℝ] PhysicalH1Sigma := physicalH1SigmaSectorCLM i
example (i : Fin 6) (u : PhysicalH1Sigma) :
    physicalH1SigmaSectorCLM i u = physicalH1SigmaSector i u := physicalH1SigmaSectorCLM_apply i u
example (i : Fin 6) (u : PhysicalH1Sigma) :
    (physicalH1SigmaSectorCLM i u).val = WithLp.toLp 2
      (Fin.cons (realFourierSector i (u.val 0))
        (fun j => realFourierSector i (u.val j.succ))) := rfl
example (i : Fin 6) (u : PhysicalH1Sigma) :
    physicalH1SigmaSector i (physicalH1SigmaSector i u) = physicalH1SigmaSector i u :=
  physicalH1SigmaSector_idempotent i u
example (i k : Fin 6) (hik : i ≠ k) (u : PhysicalH1Sigma) :
    physicalH1SigmaSector i (physicalH1SigmaSector k u) = 0 :=
  physicalH1SigmaSector_comp_eq_zero hik u
example (u : PhysicalH1Sigma) : (∑ i : Fin 6, physicalH1SigmaSector i u) = u :=
  sum_physicalH1SigmaSector u
example (i : Fin 6) (u v : PhysicalH1Sigma) :
    inner ℝ (physicalH1SigmaSector i u) v = inner ℝ u (physicalH1SigmaSector i v) :=
  inner_physicalH1SigmaSector_left i u v
example (i k : Fin 6) (hik : i ≠ k) (u v : PhysicalH1Sigma) :
    inner ℝ (physicalH1SigmaSector i u) (physicalH1SigmaSector k v) = 0 :=
  inner_physicalH1SigmaSector_eq_zero hik u v
example (u : PhysicalH1Sigma) :
    (∑ i : Fin 6, ‖physicalH1SigmaSector i u‖ ^ 2) = ‖u‖ ^ 2 :=
  sum_norm_physicalH1SigmaSector_sq u
example (u : PhysicalH1Sigma) :
    (∑ i : Fin 6, ∑ j : Fin 3, ‖(physicalH1SigmaSector i u).val j.succ‖ ^ 2) =
      ∑ j : Fin 3, ‖u.val j.succ‖ ^ 2 := physicalH1SigmaSector_enstrophy_sum u
example (i : Fin 6) (u : PhysicalH1Sigma) :
    (∑ j : Fin 3, ‖(physicalH1SigmaSector i u).val j.succ‖ ^ 2) =
      (4 * Real.pi ^ 2) * (∫ ξ : Space in sixSector i, ‖ξ‖ ^ 2 *
        ‖(𝓕 (complexifyL2 (u.val 0)) : ComplexL2) ξ‖ ^ 2) :=
  physicalH1SigmaSector_charge_eq_sector_integral i u

end QFAPhysicalH1SigmaSectors.ExpectedTypes

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourier_compLpL"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourier_compLpL
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourier_compLpL"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourier_compLpL"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourier_compLpL
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourier_compLpL"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.frequencySector_compLpL"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.frequencySector_compLpL
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.frequencySector_compLpL"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.frequencySector_compLpL"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.frequencySector_compLpL
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.frequencySector_compLpL"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourierSector_compLpL"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourierSector_compLpL
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourierSector_compLpL"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourierSector_compLpL"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourierSector_compLpL
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.fourierSector_compLpL"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexCoordinateSliceVectorCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceVector"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceVector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceVector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceVector"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceVector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceVector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceL2"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceL2"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.complexify_coordinateSliceL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.realFourierSector_coordinateSliceL2"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.realFourierSector_coordinateSliceL2
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.realFourierSector_coordinateSliceL2"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.realFourierSector_coordinateSliceL2"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.realFourierSector_coordinateSliceL2
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.realFourierSector_coordinateSliceL2"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.spatialGradientTrace_realFourierSector"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.spatialGradientTrace_realFourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.spatialGradientTrace_realFourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.spatialGradientTrace_realFourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.spatialGradientTrace_realFourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.spatialGradientTrace_realFourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.solenoidal_realFourierSector"
#check @MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.solenoidal_realFourierSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.solenoidal_realFourierSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.solenoidal_realFourierSector"
#print axioms MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.solenoidal_realFourierSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.SixSectorNaturality.solenoidal_realFourierSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_val"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_val
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_val"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_val"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_val
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_val"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_velocity"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_gradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaToH1LI_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_velocity"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_velocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_velocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_velocity"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_velocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_velocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_gradient"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_gradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_gradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_gradient"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_gradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_gradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_toH1"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_toH1
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_toH1"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_toH1"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_toH1
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_toH1"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_add"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_add
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_add"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_add
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_add"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_smul"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_smul
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_smul"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_smul"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_smul
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_smul"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_zero"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.norm_physicalH1SigmaSector_le"
#check @MethbokeAddon.QuasiFeffermanA.norm_physicalH1SigmaSector_le
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.norm_physicalH1SigmaSector_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.norm_physicalH1SigmaSector_le"
#print axioms MethbokeAddon.QuasiFeffermanA.norm_physicalH1SigmaSector_le
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.norm_physicalH1SigmaSector_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM_apply"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM_apply
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM_apply"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM_apply"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM_apply
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSectorCLM_apply"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_idempotent"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_idempotent
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_idempotent"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_idempotent"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_idempotent
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_idempotent"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_comp_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_comp_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_comp_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_comp_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_comp_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_comp_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_physicalH1SigmaSector"
#check @MethbokeAddon.QuasiFeffermanA.sum_physicalH1SigmaSector
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sum_physicalH1SigmaSector"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_physicalH1SigmaSector"
#print axioms MethbokeAddon.QuasiFeffermanA.sum_physicalH1SigmaSector
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sum_physicalH1SigmaSector"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_left"
#check @MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_left
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_left"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_left"
#print axioms MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_left
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_left"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.inner_physicalH1SigmaSector_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1SigmaSector_sq"
#check @MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1SigmaSector_sq
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1SigmaSector_sq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1SigmaSector_sq"
#print axioms MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1SigmaSector_sq
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.sum_norm_physicalH1SigmaSector_sq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_enstrophy_sum"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_enstrophy_sum
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_enstrophy_sum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_enstrophy_sum"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_enstrophy_sum
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_enstrophy_sum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_charge_eq_sector_integral"
#check @MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_charge_eq_sector_integral
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_charge_eq_sector_integral"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_charge_eq_sector_integral"
#print axioms MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_charge_eq_sector_integral
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.physicalH1SigmaSector_charge_eq_sector_integral"
