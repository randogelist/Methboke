import MethbokeAddon.QuasiFeffermanA.Contracts
import Mathlib.Analysis.Fourier.LpSpace
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# Actual real range of the vector-valued L2 Fourier transform

Componentwise real part and conjugation are constructed on the concrete
full-volume L2 carriers. Reflection is the pullback by the measure-preserving
Euclidean isometry `x ↦ -x`. Conjugate-reflection commutes with Fourier in
the precise antilinear form, proved first on complex Schwartz functions and
then by their density in L2. The real-range criterion constructs its real
preimage; it is not an assumed projector or reality interface.

Prepared for matching external compilation and complete named type/axiom
audits. No local Lean execution is authorized.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory FourierTransform ComplexConjugate
open scoped BigOperators SchwartzMap FourierTransform

namespace MethbokeAddon.QuasiFeffermanA.RealFourier

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation

/-- Actual componentwise conjugation, as a real linear Euclidean isometry. -/
def conjugateVectorLI : ComplexVector →ₗᵢ[ℝ] ComplexVector where
  toFun z := WithLp.toLp 2 (fun j : Fin 3 => Complex.conjLIE (z j))
  map_add' z w := by
    apply PiLp.ext
    intro j
    exact Complex.conjLIE.map_add (z j) (w j)
  map_smul' r z := by
    apply PiLp.ext
    intro j
    exact Complex.conjLIE.map_smul r (z j)
  norm_map' z := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_congr rfl
    intro j _
    exact congrArg (fun t : ℝ => t ^ 2) (Complex.conjLIE.norm_map (z j))

@[simp] theorem conjugateVectorLI_apply (z : ComplexVector) (j : Fin 3) :
    conjugateVectorLI z j = conj (z j) := rfl

/-- Complex scalar multiplication is conjugated, not preserved. -/
theorem conjugateVectorLI_smul (c : ℂ) (z : ComplexVector) :
    conjugateVectorLI (c • z) = conj c • conjugateVectorLI z := by
  apply PiLp.ext
  intro j
  change conj (c * z j) = conj c * conj (z j)
  exact map_mul _ _ _

private def realPartVectorLM : ComplexVector →ₗ[ℝ] Space where
  toFun z := WithLp.toLp 2 (fun j : Fin 3 => Complex.reCLM (z j))
  map_add' z w := by
    apply PiLp.ext
    intro j
    exact Complex.reCLM.map_add (z j) (w j)
  map_smul' r z := by
    apply PiLp.ext
    intro j
    exact Complex.reCLM.map_smul r (z j)

/-- Actual componentwise real part, bounded for the Euclidean vector norms. -/
def realPartVectorCLM : ComplexVector →L[ℝ] Space :=
  realPartVectorLM.mkContinuous 1 (by
    intro z
    change ‖(WithLp.toLp 2 (fun j : Fin 3 => (z j).re) : Space)‖ ≤ 1 * ‖z‖
    rw [one_mul]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
    apply Finset.sum_le_sum
    intro j _
    change ‖(z j).re‖ ^ 2 ≤ ‖z j‖ ^ 2
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    simpa only [Real.norm_eq_abs] using Complex.abs_re_le_norm (z j))

@[simp] theorem realPartVectorCLM_apply (z : ComplexVector) (j : Fin 3) :
    realPartVectorCLM z j = (z j).re := rfl

/-- A conjugation-fixed vector has its actual real part as a real preimage. -/
theorem complexify_realPartVector_of_conjugate_eq (z : ComplexVector)
    (h : conjugateVectorLI z = z) :
    complexifyVectorLI (realPartVectorCLM z) = z := by
  apply PiLp.ext
  intro j
  change ((z j).re : ℂ) = z j
  exact Complex.conj_eq_iff_re.mp (congrArg (fun w : ComplexVector => w j) h)

/-- Componentwise physical conjugation on actual L2 equivalence classes. -/
def conjugateL2CLM : ComplexL2 →L[ℝ] ComplexL2 :=
  conjugateVectorLI.toContinuousLinearMap.compLpL 2 volume

/-- The chosen conjugate representative agrees with pointwise conjugation a.e. -/
theorem conjugateL2_ae (f : ComplexL2) :
    (fun x : Space => conjugateL2CLM f x) =ᵐ[volume]
      (fun x : Space => conjugateVectorLI (f x)) :=
  conjugateVectorLI.toContinuousLinearMap.coeFn_compLpL f

/-- Physical conjugation fixes the native complexification of every real field. -/
@[simp] theorem conjugateL2_complexify (u : SpatialL2) :
    conjugateL2CLM (complexifyL2 u) = complexifyL2 u := by
  apply Lp.ext
  filter_upwards [conjugateL2_ae (complexifyL2 u), complexifyL2_ae u] with x hc hu
  rw [hc, hu]
  apply PiLp.ext
  intro j
  simp only [conjugateVectorLI_apply, complexifyVectorLI_apply, Complex.conj_ofReal]

/-- Componentwise real part on actual full-volume L2 equivalence classes. -/
def realPartL2CLM : ComplexL2 →L[ℝ] SpatialL2 :=
  realPartVectorCLM.compLpL 2 volume

/-- The real-part lift has the literal pointwise representative almost everywhere. -/
theorem realPartL2_ae (f : ComplexL2) :
    (fun x : Space => realPartL2CLM f x) =ᵐ[volume]
      (fun x : Space => realPartVectorCLM (f x)) :=
  realPartVectorCLM.coeFn_compLpL f

/-- Real part is an actual left inverse of native complexification. -/
@[simp] theorem realPartL2_complexify (u : SpatialL2) :
    realPartL2CLM (complexifyL2 u) = u := by
  apply Lp.ext
  filter_upwards [realPartL2_ae (complexifyL2 u), complexifyL2_ae u] with x hr hu
  rw [hr, hu]
  apply PiLp.ext
  intro j
  rfl

/-- Conjugation-fixed L2 classes have an explicitly constructed real preimage. -/
theorem complexify_realPartL2_of_conjugate_eq (f : ComplexL2)
    (h : conjugateL2CLM f = f) :
    complexifyL2 (realPartL2CLM f) = f := by
  apply Lp.ext
  filter_upwards [complexifyL2_ae (realPartL2CLM f), realPartL2_ae f,
    conjugateL2_ae f] with x hc hr hconj
  rw [h] at hconj
  rw [hc, hr]
  exact complexify_realPartVector_of_conjugate_eq (f x) hconj.symm

/-- Exact physical real range, with no hidden existence premise. -/
theorem exists_complexify_iff_conjugate_eq (f : ComplexL2) :
    (∃ u : SpatialL2, complexifyL2 u = f) ↔ conjugateL2CLM f = f := by
  constructor
  · rintro ⟨u, rfl⟩
    exact conjugateL2_complexify u
  · intro h
    exact ⟨realPartL2CLM f, complexify_realPartL2_of_conjugate_eq f h⟩

/-- Reflection transports full-volume a.e. statements to full-volume a.e. statements. -/
theorem ae_neg_of_ae {p : Space → Prop} (h : ∀ᵐ x : Space ∂volume, p x) :
    ∀ᵐ x : Space ∂volume, p (-x) := by
  exact (LinearIsometryEquiv.neg ℝ (E := Space)).measurePreserving.quasiMeasurePreserving.tendsto_ae.eventually h

/-- Actual pullback by the volume-preserving Euclidean reflection. -/
def reflectL2LI : ComplexL2 →ₗᵢ[ℂ] ComplexL2 :=
  Lp.compMeasurePreservingₗᵢ ℂ (LinearIsometryEquiv.neg ℝ (E := Space))
    (LinearIsometryEquiv.neg ℝ (E := Space)).measurePreserving

/-- The reflected L2 class has the reflected representative a.e. -/
theorem reflectL2_ae (f : ComplexL2) :
    (fun x : Space => reflectL2LI f x) =ᵐ[volume] (fun x : Space => f (-x)) :=
  Lp.coeFn_compMeasurePreserving f
    (LinearIsometryEquiv.neg ℝ (E := Space)).measurePreserving

/-- Conjugate-reflection on actual L2 classes, viewed as a bounded real linear map. -/
def hermitianL2CLM : ComplexL2 →L[ℝ] ComplexL2 :=
  conjugateL2CLM.comp (reflectL2LI.toContinuousLinearMap.restrictScalars ℝ)

/-- The actual Hermitian involution is pointwise conjugate-reflection a.e. -/
theorem hermitianL2_ae (f : ComplexL2) :
    (fun x : Space => hermitianL2CLM f x) =ᵐ[volume]
      (fun x : Space => conjugateVectorLI (f (-x))) := by
  filter_upwards [conjugateL2_ae (reflectL2LI f), reflectL2_ae f] with x hc hr
  change conjugateL2CLM (reflectL2LI f) x = conjugateVectorLI (f (-x))
  rw [hc, hr]

private theorem conjugateL2_toLp (φ : 𝓢(Space, ComplexVector)) :
    conjugateL2CLM (φ.toLp 2 volume) =
      (φ.postcompCLM conjugateVectorLI.toContinuousLinearMap).toLp 2 volume := by
  apply Lp.ext
  filter_upwards [conjugateL2_ae (φ.toLp 2 volume), φ.coeFn_toLp 2 volume,
    (φ.postcompCLM conjugateVectorLI.toContinuousLinearMap).coeFn_toLp 2 volume]
    with x hc hφ hpost
  rw [hc, hφ, hpost]
  rfl

private theorem fourier_postcomp_conjugate (φ : 𝓢(Space, ComplexVector)) (ξ : Space) :
    (𝓕 (φ.postcompCLM conjugateVectorLI.toContinuousLinearMap) :
      𝓢(Space, ComplexVector)) ξ =
        conjugateVectorLI ((𝓕 φ : 𝓢(Space, ComplexVector)) (-ξ)) := by
  change (∫ x : Space, Real.fourierChar (-inner ℝ x ξ) •
      conjugateVectorLI (φ x)) =
    conjugateVectorLI (∫ x : Space, Real.fourierChar (-inner ℝ x (-ξ)) • φ x)
  rw [← conjugateVectorLI.integral_comp_comm]
  apply integral_congr_ae
  filter_upwards with x
  simp only [inner_neg_right, neg_neg, Circle.smul_def, conjugateVectorLI_smul,
    Circle.starRingEnd_addChar]

/-- The complete actual L2 conjugation/Fourier transport identity, derived by
complex Schwartz density and continuity of both constructed L2 maps. -/
theorem fourier_conjugateL2 (f : ComplexL2) :
    𝓕 (conjugateL2CLM f) = hermitianL2CLM (𝓕 f) := by
  set p := fun f : ComplexL2 => 𝓕 (conjugateL2CLM f) = hermitianL2CLM (𝓕 f)
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := Space) (F := ComplexVector)
      (p := 2) (μ := volume) ENNReal.ofNat_ne_top) f
  · apply isClosed_eq
    · exact (Lp.fourierTransformₗᵢ Space ComplexVector).continuous.comp
        conjugateL2CLM.continuous
    · exact hermitianL2CLM.continuous.comp
        (Lp.fourierTransformₗᵢ Space ComplexVector).continuous
  intro φ
  change 𝓕 (conjugateL2CLM (φ.toLp 2 volume)) =
    hermitianL2CLM (𝓕 (φ.toLp 2 volume))
  rw [conjugateL2_toLp]
  simp only [SchwartzMap.toLp_fourier_eq]
  apply Lp.ext
  filter_upwards [(𝓕 (φ.postcompCLM conjugateVectorLI.toContinuousLinearMap) :
      𝓢(Space, ComplexVector)).coeFn_toLp 2 volume,
    hermitianL2_ae ((𝓕 φ : 𝓢(Space, ComplexVector)).toLp 2 volume),
    ae_neg_of_ae ((𝓕 φ : 𝓢(Space, ComplexVector)).coeFn_toLp 2 volume)]
    with ξ hleft hright hneg
  rw [hleft, hright, hneg]
  exact fourier_postcomp_conjugate φ ξ

/-- Fourier images of actual real fields satisfy the constructed Hermitian symmetry. -/
theorem hermitian_fourier_complexify (u : SpatialL2) :
    hermitianL2CLM (𝓕 (complexifyL2 u)) = 𝓕 (complexifyL2 u) := by
  rw [← fourier_conjugateL2, conjugateL2_complexify]

/-- Physical reality and Fourier Hermitian symmetry are equivalent by Fourier injectivity. -/
theorem conjugate_eq_iff_hermitian_fourier_eq (f : ComplexL2) :
    conjugateL2CLM f = f ↔ hermitianL2CLM (𝓕 f) = 𝓕 f := by
  constructor
  · intro h
    rw [← fourier_conjugateL2, h]
  · intro h
    apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
    change 𝓕 (conjugateL2CLM f) = 𝓕 f
    rw [fourier_conjugateL2, h]

/-- Exact real Fourier-range criterion on actual L2 classes. -/
theorem exists_complexify_iff_hermitian_fourier_eq (f : ComplexL2) :
    (∃ u : SpatialL2, complexifyL2 u = f) ↔ hermitianL2CLM (𝓕 f) = 𝓕 f :=
  (exists_complexify_iff_conjugate_eq f).trans
    (conjugate_eq_iff_hermitian_fourier_eq f)

/-- A frequency-side L2 class is the Fourier transform of an actual real L2
field exactly when it has the actual conjugate-reflection symmetry. -/
theorem exists_fourier_complexify_iff_hermitian_eq (f : ComplexL2) :
    (∃ u : SpatialL2, 𝓕 (complexifyL2 u) = f) ↔ hermitianL2CLM f = f := by
  constructor
  · rintro ⟨u, rfl⟩
    exact hermitian_fourier_complexify u
  · intro h
    have hreal : conjugateL2CLM (𝓕⁻ f) = 𝓕⁻ f := by
      apply (conjugate_eq_iff_hermitian_fourier_eq (𝓕⁻ f)).mpr
      simpa only [fourier_fourierInv_eq] using h
    obtain ⟨u, hu⟩ := (exists_complexify_iff_conjugate_eq (𝓕⁻ f)).mpr hreal
    refine ⟨u, ?_⟩
    rw [hu, fourier_fourierInv_eq]

end MethbokeAddon.QuasiFeffermanA.RealFourier
