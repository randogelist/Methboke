import MethbokeAddon.QuasiFeffermanA.PhysicalH1Sectors
import MethbokeAddon.QuasiFeffermanA.PhysicalH1Divergence

/-!
# Coordinate naturality and actual solenoidal sector preservation

Complex linear codomain maps commute with the native L2 Fourier transform,
first by the integrable Schwartz formula and then by density. The scalar
sector indicators commute with the same maps. Actual real coordinate slices
therefore commute with the real Fourier sector projections after injective
complexification. This transports the constructed physical divergence trace
and proves native solenoidal preservation without assuming that conclusion.

Prepared source requires matching cached external compiler/type/axiom evidence.
No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform SchwartzMap

namespace MethbokeAddon.QuasiFeffermanA.SixSectorNaturality

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open RealSectorMultipliers SixSectorMultipliers PhysicalH1Divergence

private theorem compLpL_toLp (A : ComplexVector →L[ℂ] ComplexVector)
    (φ : 𝓢(Space, ComplexVector)) :
    A.compLpL 2 volume (φ.toLp 2 volume) = (φ.postcompCLM A).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [A.coeFn_compLpL (φ.toLp 2 volume), φ.coeFn_toLp 2 volume,
    (φ.postcompCLM A).coeFn_toLp 2 volume] with x hA hφ hpost
  rw [hA, hφ, hpost]
  rfl

private theorem fourier_postcompCLM (A : ComplexVector →L[ℂ] ComplexVector)
    (φ : 𝓢(Space, ComplexVector)) (ξ : Space) :
    (𝓕 (φ.postcompCLM A) : 𝓢(Space, ComplexVector)) ξ =
      A ((𝓕 φ : 𝓢(Space, ComplexVector)) ξ) := by
  change (∫ x : Space, Real.fourierChar (-inner ℝ x ξ) • A (φ x)) =
    A (∫ x : Space, Real.fourierChar (-inner ℝ x ξ) • φ x)
  rw [← A.integral_comp_comm ((Real.fourierIntegral_convergent_iff ξ).mpr φ.integrable)]
  apply integral_congr_ae
  filter_upwards with x
  simp only [Circle.smul_def, map_smul]

/-- Native L2 Fourier transformation commutes with every bounded complex-linear
endomorphism of the actual vector codomain. No pointwise L2 Fourier integral
or extra integrability premise is assumed. -/
theorem fourier_compLpL (A : ComplexVector →L[ℂ] ComplexVector) (f : ComplexL2) :
    𝓕 (A.compLpL 2 volume f) = A.compLpL 2 volume (𝓕 f) := by
  set p := fun f : ComplexL2 => 𝓕 (A.compLpL 2 volume f) = A.compLpL 2 volume (𝓕 f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := Space) (F := ComplexVector)
      (p := 2) (μ := volume) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ Space ComplexVector).continuous.comp
        (A.compLpL 2 volume).continuous
    · exact (A.compLpL 2 volume).continuous.comp
        (Lp.fourierTransformₗᵢ Space ComplexVector).continuous
  intro φ
  change 𝓕 (A.compLpL 2 volume (φ.toLp 2 volume)) =
    A.compLpL 2 volume (𝓕 (φ.toLp 2 volume))
  rw [compLpL_toLp]
  simp only [SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (φ.postcompCLM A) : 𝓢(Space, ComplexVector)).coeFn_toLp 2 volume,
    A.coeFn_compLpL ((𝓕 φ : 𝓢(Space, ComplexVector)).toLp 2 volume),
    (𝓕 φ : 𝓢(Space, ComplexVector)).coeFn_toLp 2 volume]
    with ξ hleft hright hφ
  rw [hleft, hright, hφ]
  exact fourier_postcompCLM A φ ξ

/-- The actual scalar indicator restriction commutes with every such codomain map. -/
theorem frequencySector_compLpL (i : Fin 6) (A : ComplexVector →L[ℂ] ComplexVector)
    (f : ComplexL2) :
    frequencySector i (A.compLpL 2 volume f) =
      A.compLpL 2 volume (frequencySector i f) := by
  apply Lp.ext
  filter_upwards [frequencySector_ae i (A.compLpL 2 volume f), A.coeFn_compLpL f,
    A.coeFn_compLpL (frequencySector i f), frequencySector_ae i f]
    with ξ houter hsource htarget hinner
  rw [houter, htarget, hinner]
  by_cases h : ξ ∈ sixSector i
  · simp only [Set.indicator_of_mem h, hsource]
  · simp only [Set.indicator_of_notMem h, map_zero]

/-- Fourier-conjugate sector projections retain actual codomain naturality. -/
theorem fourierSector_compLpL (i : Fin 6) (A : ComplexVector →L[ℂ] ComplexVector)
    (f : ComplexL2) :
    fourierSector i (A.compLpL 2 volume f) = A.compLpL 2 volume (fourierSector i f) := by
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  change 𝓕 (fourierSector i (A.compLpL 2 volume f)) =
    𝓕 (A.compLpL 2 volume (fourierSector i f))
  simp only [fourier_fourierSector, fourier_compLpL, frequencySector_compLpL]

/-- The actual complex extension of the coordinate slice v ↦ v_j e_0. -/
def complexCoordinateSliceVectorCLM (j : Fin 3) : ComplexVector →L[ℂ] ComplexVector :=
  (PiLp.proj 2 (fun _ : Fin 3 => ℂ) j).smulRight
    (EuclideanSpace.single 0 (1 : ℂ))

@[simp] theorem complexCoordinateSliceVectorCLM_apply (j : Fin 3) (z : ComplexVector) :
    complexCoordinateSliceVectorCLM j z = (z j) • EuclideanSpace.single 0 (1 : ℂ) := rfl

/-- Exact coordinate compatibility of the native componentwise complexification. -/
theorem complexify_coordinateSliceVector (j : Fin 3) (v : Space) :
    complexifyVectorLI (coordinateSliceVectorCLM j v) =
      complexCoordinateSliceVectorCLM j (complexifyVectorLI v) := by
  apply PiLp.ext
  intro k
  simp only [complexifyVectorLI_apply, coordinateSliceVectorCLM_apply,
    complexCoordinateSliceVectorCLM_apply, PiLp.smul_apply,
    coordinateVector, PiLp.single_apply, smul_eq_mul]
  split_ifs <;> simp

/-- The same compatibility holds for actual L2 classes, not only representatives. -/
theorem complexify_coordinateSliceL2 (j : Fin 3) (u : SpatialL2) :
    complexifyL2 (coordinateSliceL2 j u) =
      (complexCoordinateSliceVectorCLM j).compLpL 2 volume (complexifyL2 u) := by
  apply Lp.ext
  filter_upwards [complexifyL2_ae (coordinateSliceL2 j u), coordinateSliceL2_ae j u,
    (complexCoordinateSliceVectorCLM j).coeFn_compLpL (complexifyL2 u), complexifyL2_ae u]
    with x hleft hreal hright hcomplex
  rw [hleft, hreal, hright, hcomplex]
  exact complexify_coordinateSliceVector j (u x)

/-- The constructed real sector projection commutes with the actual coordinate
slice entering the native divergence trace. -/
theorem realFourierSector_coordinateSliceL2 (i : Fin 6) (j : Fin 3) (u : SpatialL2) :
    realFourierSector i (coordinateSliceL2 j u) =
      coordinateSliceL2 j (realFourierSector i u) := by
  apply complexifyL2LI.injective
  change complexifyL2 (realFourierSector i (coordinateSliceL2 j u)) =
    complexifyL2 (coordinateSliceL2 j (realFourierSector i u))
  simp only [complexify_realFourierSector, complexify_coordinateSliceL2,
    fourierSector_compLpL]

/-- The full weak-gradient trace commutes with the actual real sector operator. -/
theorem spatialGradientTrace_realFourierSector (i : Fin 6) (G : Fin 3 → SpatialL2) :
    spatialGradientTrace (fun j => realFourierSector i (G j)) =
      realFourierSector i (spatialGradientTrace G) := by
  unfold spatialGradientTrace
  change (∑ j : Fin 3, coordinateSliceL2 j (realFourierSector i (G j))) =
    realFourierSectorCLM i (∑ j : Fin 3, coordinateSliceL2 j (G j))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact (realFourierSector_coordinateSliceL2 i j (G j)).symm

/-- Native compact-test solenoidality is preserved for a supplied actual H1
velocity and weak gradient. The projected derivative and divergence claims
are both derived, rather than included among the hypotheses. -/
theorem solenoidal_realFourierSector (i : Fin 6)
    {v : SpatialL2} {G : Fin 3 → SpatialL2}
    (hweak : SpatialWeakGradient v G) (hsol : Solenoidal v) :
    Solenoidal (realFourierSector i v) := by
  apply (spatialWeakGradient_solenoidal_iff_trace_eq_zero
    (spatialWeakGradient_realFourierSector i hweak)).mpr
  rw [spatialGradientTrace_realFourierSector,
    (spatialWeakGradient_solenoidal_iff_trace_eq_zero hweak).mp hsol,
    realFourierSector_zero]

end MethbokeAddon.QuasiFeffermanA.SixSectorNaturality
