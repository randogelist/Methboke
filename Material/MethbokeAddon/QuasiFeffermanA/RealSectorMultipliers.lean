import MethbokeAddon.QuasiFeffermanA.RealFourier
import MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers

/-!
# Actual real L2 Fourier sector projections

Evenness of the literal six sectors proves preservation of the constructed
Hermitian Fourier range. Real part therefore transports the admitted complex
L2 projections to actual full-volume real vector L2 projections. Every
algebraic and norm property refers to these constructed operators.

Physical H1 gradient transport, solenoidal restriction and physical Fourier
charge identities are subsequent layers. Matching external verification of
this source and its independent type consumers is required.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

namespace MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open MethbokeAddon.QuasiFeffermanA.RealFourier
open MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers

/-- The literal even real frequency restriction commutes with conjugate-reflection. -/
theorem hermitian_frequencySector (i : Fin 6) (f : ComplexL2) :
    hermitianL2CLM (frequencySector i f) = frequencySector i (hermitianL2CLM f) := by
  apply Lp.ext
  filter_upwards [hermitianL2_ae (frequencySector i f),
    ae_neg_of_ae (frequencySector_ae i f),
    frequencySector_ae i (hermitianL2CLM f), hermitianL2_ae f]
    with ξ hj hneg hp hf
  rw [hj, hneg, hp]
  by_cases h : ξ ∈ sixSector i
  · have hn : -ξ ∈ sixSector i := (mem_sixSector_neg_iff i ξ).mpr h
    simp only [Set.indicator_of_mem h, Set.indicator_of_mem hn, hf]
  · have hn : -ξ ∉ sixSector i := fun hn => h ((mem_sixSector_neg_iff i ξ).mp hn)
    simp only [Set.indicator_of_notMem h, Set.indicator_of_notMem hn, map_zero]

/-- Every actual complex sector projection of a real input remains physically real. -/
theorem conjugate_fourierSector_complexify (i : Fin 6) (u : SpatialL2) :
    conjugateL2CLM (fourierSector i (complexifyL2 u)) =
      fourierSector i (complexifyL2 u) := by
  apply (conjugate_eq_iff_hermitian_fourier_eq _).mpr
  rw [fourier_fourierSector, hermitian_frequencySector, hermitian_fourier_complexify]

/-- The actual real L2 projection obtained from the even complex Fourier multiplier. -/
def realFourierSector (i : Fin 6) (u : SpatialL2) : SpatialL2 :=
  realPartL2CLM (fourierSector i (complexifyL2 u))

/-- Exact embedding into the admitted complex Fourier projection. -/
theorem complexify_realFourierSector (i : Fin 6) (u : SpatialL2) :
    complexifyL2 (realFourierSector i u) = fourierSector i (complexifyL2 u) :=
  complexify_realPartL2_of_conjugate_eq _ (conjugate_fourierSector_complexify i u)

/-- The real operator is packaged by composition of actual bounded real linear maps. -/
def realFourierSectorCLM (i : Fin 6) : SpatialL2 →L[ℝ] SpatialL2 :=
  realPartL2CLM.comp (((fourierSectorCLM i).restrictScalars ℝ).comp
    complexifyL2LI.toContinuousLinearMap)

@[simp] theorem realFourierSectorCLM_apply (i : Fin 6) (u : SpatialL2) :
    realFourierSectorCLM i u = realFourierSector i u := rfl

/-- The constructed real projection is additive. -/
theorem realFourierSector_add (i : Fin 6) (u v : SpatialL2) :
    realFourierSector i (u + v) = realFourierSector i u + realFourierSector i v :=
  (realFourierSectorCLM i).map_add u v

/-- The constructed real projection is homogeneous over the actual real scalar field. -/
theorem realFourierSector_smul (i : Fin 6) (r : ℝ) (u : SpatialL2) :
    realFourierSector i (r • u) = r • realFourierSector i u :=
  (realFourierSectorCLM i).map_smul r u

@[simp] theorem realFourierSector_zero (i : Fin 6) : realFourierSector i 0 = 0 :=
  (realFourierSectorCLM i).map_zero

/-- Real contraction has the same exact bound one as the complex projection. -/
theorem norm_realFourierSector_le (i : Fin 6) (u : SpatialL2) :
    ‖realFourierSector i u‖ ≤ ‖u‖ := by
  rw [← complexifyL2_norm (realFourierSector i u), complexify_realFourierSector]
  exact (norm_fourierSector_le i (complexifyL2 u)).trans_eq (complexifyL2_norm u)

/-- Each constructed real projection is idempotent. -/
theorem realFourierSector_idempotent (i : Fin 6) (u : SpatialL2) :
    realFourierSector i (realFourierSector i u) = realFourierSector i u := by
  apply complexifyL2LI.injective
  change complexifyL2 (realFourierSector i (realFourierSector i u)) =
    complexifyL2 (realFourierSector i u)
  simp only [complexify_realFourierSector, fourierSector_idempotent]

/-- Distinct real sector projections annihilate one another. -/
theorem realFourierSector_comp_eq_zero {i j : Fin 6} (hij : i ≠ j) (u : SpatialL2) :
    realFourierSector i (realFourierSector j u) = 0 := by
  apply complexifyL2LI.injective
  change complexifyL2 (realFourierSector i (realFourierSector j u)) = complexifyL2 0
  simp only [complexify_realFourierSector, fourierSector_comp_eq_zero hij,
    complexifyL2_zero]

/-- The six actual real Fourier projections reconstruct every real L2 class. -/
theorem sum_realFourierSector (u : SpatialL2) :
    ∑ i : Fin 6, realFourierSector i u = u := by
  apply complexifyL2LI.injective
  change complexifyL2LI (∑ i : Fin 6, realFourierSector i u) = complexifyL2 u
  rw [map_sum]
  change (∑ i : Fin 6, complexifyL2 (realFourierSector i u)) = complexifyL2 u
  simp only [complexify_realFourierSector, sum_fourierSector]

private theorem real_inner_complexify (u v : SpatialL2) :
    inner ℝ u v = Complex.re (inner ℂ (complexifyL2 u) (complexifyL2 v)) := by
  letI : InnerProductSpace ℝ ComplexL2 := InnerProductSpace.rclikeToReal ℂ ComplexL2
  exact (complexifyL2LI.inner_map_map u v).symm

/-- Actual real self-adjointness follows from isometric complexification. -/
theorem inner_realFourierSector_left (i : Fin 6) (u v : SpatialL2) :
    inner ℝ (realFourierSector i u) v = inner ℝ u (realFourierSector i v) := by
  rw [real_inner_complexify, real_inner_complexify,
    complexify_realFourierSector, complexify_realFourierSector,
    inner_fourierSector_left]

/-- Different real sector outputs are orthogonal for arbitrary real inputs. -/
theorem inner_realFourierSector_eq_zero {i j : Fin 6} (hij : i ≠ j) (u v : SpatialL2) :
    inner ℝ (realFourierSector i u) (realFourierSector j v) = 0 := by
  rw [real_inner_complexify, complexify_realFourierSector, complexify_realFourierSector,
    inner_fourierSector_eq_zero hij]
  rfl

/-- Exact full-volume real L2 squared-norm decomposition. -/
theorem sum_norm_realFourierSector_sq (u : SpatialL2) :
    (∑ i : Fin 6, ‖realFourierSector i u‖ ^ 2) = ‖u‖ ^ 2 := by
  calc
    (∑ i : Fin 6, ‖realFourierSector i u‖ ^ 2) =
        ∑ i : Fin 6, ‖fourierSector i (complexifyL2 u)‖ ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← complexifyL2_norm (realFourierSector i u), complexify_realFourierSector]
    _ = ‖complexifyL2 u‖ ^ 2 := sum_norm_fourierSector_sq (complexifyL2 u)
    _ = ‖u‖ ^ 2 := by rw [complexifyL2_norm]

end MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers
