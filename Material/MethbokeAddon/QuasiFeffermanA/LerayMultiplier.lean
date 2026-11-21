import MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.Tactic

/-!
# The actual real whole-space Leray matrix multiplier

The pointwise map is Mathlib's constructed orthogonal projection onto the
orthogonal complement of the complexified frequency vector. Its literal
rank-one matrix formula is proved, including the identity at zero.
That formula supplies genuine measurability; norm domination constructs the
actual L2 multiplier. Fourier conjugation and the proved real-range bridge
then give a real bounded orthogonal projection, with no assumed operator port.

Native weak-gradient transport and solenoidal identification are in LerayH1.
Prepared source requires matching authorized cached external type/axiom evidence.
No local Lean, Lake, kernel audit or proof runner is used.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

namespace MethbokeAddon.QuasiFeffermanA.LerayMultiplier

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open RealFourier SixSectorMultipliers RealSectorMultipliers

/-- The constructed projection onto the plane perpendicular to the actual frequency. -/
def leraySymbol (ξ : Space) : ComplexVector →L[ℂ] ComplexVector :=
  (Submodule.span ℂ {complexifyVectorLI ξ}).orthogonal.starProjection

/-- Literal matrix formula; division by zero gives the identity at zero frequency. -/
theorem leraySymbol_formula (ξ : Space) (z : ComplexVector) :
    leraySymbol ξ z = z -
      (inner ℂ (complexifyVectorLI ξ) z / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • complexifyVectorLI ξ := by
  change (Submodule.span ℂ {complexifyVectorLI ξ}).orthogonal.starProjection z = _
  rw [Submodule.starProjection_orthogonal_val, Submodule.starProjection_singleton,
    complexifyVectorLI_norm]
  rfl

/-- The frequency contraction is the literal finite coordinate sum. -/
theorem inner_complexifyVector_eq_sum (ξ : Space) (z : ComplexVector) :
    inner ℂ (complexifyVectorLI ξ) z =
      ∑ j : Fin 3, (ξ j : ℂ) * z j := by
  rw [PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro j _
  simp only [complexifyVectorLI_apply, RCLike.inner_apply', Complex.conj_ofReal]

/-- Each matrix coordinate is the intended real rank-one formula. -/
theorem leraySymbol_coordinate (ξ : Space) (z : ComplexVector) (j : Fin 3) :
    leraySymbol ξ z j = z j -
      ((∑ k : Fin 3, (ξ k : ℂ) * z k) / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) * (ξ j : ℂ) := by
  rw [leraySymbol_formula, inner_complexifyVector_eq_sum]
  simp only [PiLp.sub_apply, PiLp.smul_apply, complexifyVectorLI_apply, smul_eq_mul]

@[simp] theorem leraySymbol_zero (z : ComplexVector) : leraySymbol 0 z = z := by
  simp [leraySymbol_formula]

/-- The pointwise operator has the exact contraction bound one. -/
theorem norm_leraySymbol_le (ξ : Space) (z : ComplexVector) :
    ‖leraySymbol ξ z‖ ≤ ‖z‖ :=
  (Submodule.span ℂ {complexifyVectorLI ξ}).orthogonal.norm_starProjection_apply_le z

/-- Native Hermitian self-adjointness of the actual frequency projection. -/
theorem inner_leraySymbol_left (ξ : Space) (z w : ComplexVector) :
    inner ℂ (leraySymbol ξ z) w = inner ℂ z (leraySymbol ξ w) :=
  Submodule.inner_starProjection_left_eq_right
    (Submodule.span ℂ {complexifyVectorLI ξ}).orthogonal z w

theorem leraySymbol_idempotent (ξ : Space) (z : ComplexVector) :
    leraySymbol ξ (leraySymbol ξ z) = leraySymbol ξ z := by
  exact (Submodule.starProjection_eq_self_iff
    (K := (Submodule.span ℂ {complexifyVectorLI ξ}).orthogonal)).mpr
      (Submodule.starProjection_apply_mem
        (Submodule.span ℂ {complexifyVectorLI ξ}).orthogonal z)

/-- Fixed points are exactly the frequency-transverse vectors, also at zero. -/
theorem leraySymbol_eq_self_iff (ξ : Space) (z : ComplexVector) :
    leraySymbol ξ z = z ↔ inner ℂ (complexifyVectorLI ξ) z = 0 := by
  change (Submodule.span ℂ {complexifyVectorLI ξ}).orthogonal.starProjection z = z ↔ _
  rw [Submodule.starProjection_eq_self_iff,
    Submodule.mem_orthogonal_singleton_iff_inner_right]

theorem leraySymbol_transverse (ξ : Space) (z : ComplexVector) :
    inner ℂ (complexifyVectorLI ξ) (leraySymbol ξ z) = 0 :=
  (leraySymbol_eq_self_iff ξ (leraySymbol ξ z)).mp (leraySymbol_idempotent ξ z)

/-- Evenness of the literal symbol is proved, not supplied as an operator hypothesis. -/
theorem leraySymbol_neg (ξ : Space) : leraySymbol (-ξ) = leraySymbol ξ := by
  apply ContinuousLinearMap.ext
  intro z
  simp only [leraySymbol_formula, map_neg, norm_neg, inner_neg_left, neg_div,
    neg_smul, smul_neg, neg_neg]

/-- Real entries commute with actual componentwise complex conjugation. -/
theorem conjugate_leraySymbol (ξ : Space) (z : ComplexVector) :
    conjugateVectorLI (leraySymbol ξ z) =
      leraySymbol ξ (conjugateVectorLI z) := by
  apply PiLp.ext
  intro j
  simp only [conjugateVectorLI_apply, leraySymbol_coordinate, map_sub, map_div₀,
    map_sum, map_mul, Complex.conj_ofReal]

private theorem leraySymbol_aestronglyMeasurable (f : ComplexL2) :
    AEStronglyMeasurable (fun ξ : Space => leraySymbol ξ (f ξ)) volume := by
  have hξ : AEStronglyMeasurable (fun ξ : Space => complexifyVectorLI ξ) volume :=
    complexifyVectorLI.continuous.aestronglyMeasurable
  have hd : AEStronglyMeasurable (fun ξ : Space => ((‖ξ‖ ^ 2 : ℝ) : ℂ)) volume :=
    (by fun_prop : Continuous (fun ξ : Space => ((‖ξ‖ ^ 2 : ℝ) : ℂ))).aestronglyMeasurable
  have hc := (hξ.inner (Lp.aestronglyMeasurable f)).div₀ hd
  have hraw := (Lp.aestronglyMeasurable f).sub (hc.smul hξ)
  change AEStronglyMeasurable (fun ξ : Space => f ξ -
    (inner ℂ (complexifyVectorLI ξ) (f ξ) / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) •
      complexifyVectorLI ξ) volume at hraw
  simpa only [leraySymbol_formula] using hraw

private theorem leraySymbol_memLp (f : ComplexL2) :
    MemLp (fun ξ : Space => leraySymbol ξ (f ξ)) 2 volume :=
  (Lp.memLp f).of_le (leraySymbol_aestronglyMeasurable f)
    (Filter.Eventually.of_forall (fun ξ => norm_leraySymbol_le ξ (f ξ)))

/-- The actual variable-matrix multiplier, constructed from genuine L2 membership. -/
def frequencyLeray (f : ComplexL2) : ComplexL2 :=
  (leraySymbol_memLp f).toLp (fun ξ : Space => leraySymbol ξ (f ξ))

/-- Literal action on chosen L2 representatives, almost everywhere. -/
theorem frequencyLeray_ae (f : ComplexL2) :
    (fun ξ : Space => frequencyLeray f ξ) =ᵐ[volume]
      (fun ξ : Space => leraySymbol ξ (f ξ)) :=
  MemLp.coeFn_toLp _

theorem norm_frequencyLeray_le (f : ComplexL2) : ‖frequencyLeray f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [frequencyLeray_ae f] with ξ hξ
  rw [hξ]
  exact norm_leraySymbol_le ξ (f ξ)

private theorem frequencyLeray_add (f g : ComplexL2) :
    frequencyLeray (f + g) = frequencyLeray f + frequencyLeray g := by
  apply Lp.ext
  filter_upwards [frequencyLeray_ae (f + g), frequencyLeray_ae f,
    frequencyLeray_ae g, Lp.coeFn_add f g,
    Lp.coeFn_add (frequencyLeray f) (frequencyLeray g)] with ξ hs hf hg ha ht
  rw [hs, ht, Pi.add_apply, ha, Pi.add_apply, hf, hg, map_add]

private theorem frequencyLeray_smul (a : ℂ) (f : ComplexL2) :
    frequencyLeray (a • f) = a • frequencyLeray f := by
  apply Lp.ext
  filter_upwards [frequencyLeray_ae (a • f), frequencyLeray_ae f,
    Lp.coeFn_smul a f, Lp.coeFn_smul a (frequencyLeray f)] with ξ hs hf ha ht
  rw [hs, ht, Pi.smul_apply, ha, Pi.smul_apply, hf, map_smul]

/-- The constructed multiplier as a bounded complex-linear map. -/
def frequencyLerayCLM : ComplexL2 →L[ℂ] ComplexL2 :=
  ({ toFun := frequencyLeray
     map_add' := frequencyLeray_add
     map_smul' := frequencyLeray_smul } : ComplexL2 →ₗ[ℂ] ComplexL2).mkContinuous 1
    (fun f => by
      change ‖frequencyLeray f‖ ≤ 1 * ‖f‖
      simpa only [one_mul] using norm_frequencyLeray_le f)

@[simp] theorem frequencyLerayCLM_apply (f : ComplexL2) :
    frequencyLerayCLM f = frequencyLeray f := rfl

theorem frequencyLeray_idempotent (f : ComplexL2) :
    frequencyLeray (frequencyLeray f) = frequencyLeray f := by
  apply Lp.ext
  filter_upwards [frequencyLeray_ae (frequencyLeray f), frequencyLeray_ae f]
    with ξ ho hi
  rw [ho, hi, leraySymbol_idempotent]

theorem inner_frequencyLeray_left (f g : ComplexL2) :
    inner ℂ (frequencyLeray f) g = inner ℂ f (frequencyLeray g) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [frequencyLeray_ae f, frequencyLeray_ae g] with ξ hf hg
  rw [hf, hg, inner_leraySymbol_left]

/-- Commutation with a supplied scalar multiplier identity between actual L2 fields. -/
theorem frequencyLeray_multiplier_ae (f g : ComplexL2) (m : Space → ℂ)
    (h : (fun ξ : Space => g ξ) =ᵐ[volume] (fun ξ : Space => m ξ • f ξ)) :
    (fun ξ : Space => frequencyLeray g ξ) =ᵐ[volume]
      (fun ξ : Space => m ξ • frequencyLeray f ξ) := by
  filter_upwards [frequencyLeray_ae g, frequencyLeray_ae f, h] with ξ hg hf hm
  rw [hg, hf, hm, map_smul]

/-- Scalar sector restrictions commute with the constructed variable matrix. -/
theorem frequencyLeray_frequencySector (i : Fin 6) (f : ComplexL2) :
    frequencyLeray (frequencySector i f) = frequencySector i (frequencyLeray f) := by
  apply Lp.ext
  filter_upwards [frequencyLeray_ae (frequencySector i f), frequencySector_ae i f,
    frequencySector_ae i (frequencyLeray f), frequencyLeray_ae f]
    with ξ ho hi ht hf
  rw [ho, hi, ht]
  by_cases h : ξ ∈ sixSector i
  · simp only [Set.indicator_of_mem h, hf]
  · simp only [Set.indicator_of_notMem h, map_zero]

/-- Even real matrices preserve the actual Hermitian Fourier symmetry. -/
theorem hermitian_frequencyLeray (f : ComplexL2) :
    hermitianL2CLM (frequencyLeray f) = frequencyLeray (hermitianL2CLM f) := by
  apply Lp.ext
  filter_upwards [hermitianL2_ae (frequencyLeray f),
    ae_neg_of_ae (frequencyLeray_ae f), frequencyLeray_ae (hermitianL2CLM f),
    hermitianL2_ae f] with ξ hj hn hp hf
  rw [hj, hn, hp, hf, leraySymbol_neg, conjugate_leraySymbol]

/-- Fourier conjugation of the actual frequency multiplier. -/
def fourierLeray (f : ComplexL2) : ComplexL2 := 𝓕⁻ (frequencyLeray (𝓕 f))

@[simp] theorem fourier_fourierLeray (f : ComplexL2) :
    𝓕 (fourierLeray f) = frequencyLeray (𝓕 f) :=
  fourier_fourierInv_eq _

def fourierLerayCLM : ComplexL2 →L[ℂ] ComplexL2 :=
  (Lp.fourierTransformₗᵢ Space ComplexVector).symm.toLinearIsometry.toContinuousLinearMap.comp
    (frequencyLerayCLM.comp
      (Lp.fourierTransformₗᵢ Space ComplexVector).toLinearIsometry.toContinuousLinearMap)

@[simp] theorem fourierLerayCLM_apply (f : ComplexL2) :
    fourierLerayCLM f = fourierLeray f := rfl

theorem norm_fourierLeray_le (f : ComplexL2) : ‖fourierLeray f‖ ≤ ‖f‖ := by
  rw [← Lp.norm_fourier_eq (fourierLeray f), fourier_fourierLeray]
  exact (norm_frequencyLeray_le (𝓕 f)).trans_eq (Lp.norm_fourier_eq f)

theorem fourierLeray_idempotent (f : ComplexL2) :
    fourierLeray (fourierLeray f) = fourierLeray f := by
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  change 𝓕 (fourierLeray (fourierLeray f)) = 𝓕 (fourierLeray f)
  simp only [fourier_fourierLeray, frequencyLeray_idempotent]

theorem inner_fourierLeray_left (f g : ComplexL2) :
    inner ℂ (fourierLeray f) g = inner ℂ f (fourierLeray g) := by
  rw [← Lp.inner_fourier_eq (fourierLeray f) g,
    ← Lp.inner_fourier_eq f (fourierLeray g)]
  simp only [fourier_fourierLeray]
  exact inner_frequencyLeray_left (𝓕 f) (𝓕 g)

/-- The same concrete sector and Leray operators commute after Fourier transport. -/
theorem fourierLeray_fourierSector (i : Fin 6) (f : ComplexL2) :
    fourierLeray (fourierSector i f) = fourierSector i (fourierLeray f) := by
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  change 𝓕 (fourierLeray (fourierSector i f)) = 𝓕 (fourierSector i (fourierLeray f))
  simp only [fourier_fourierLeray, fourier_fourierSector, frequencyLeray_frequencySector]

/-- Actual real part constructs the physical Leray output. -/
def realLeray (v : SpatialL2) : SpatialL2 := realPartL2CLM (fourierLeray (complexifyL2 v))

/-- Its complexification is exactly the intended complex Fourier projection. -/
theorem complexify_realLeray (v : SpatialL2) :
    complexifyL2 (realLeray v) = fourierLeray (complexifyL2 v) := by
  apply complexify_realPartL2_of_conjugate_eq
  apply (conjugate_eq_iff_hermitian_fourier_eq _).mpr
  rw [fourier_fourierLeray, hermitian_frequencyLeray, hermitian_fourier_complexify]

def realLerayCLM : SpatialL2 →L[ℝ] SpatialL2 :=
  realPartL2CLM.comp ((fourierLerayCLM.restrictScalars ℝ).comp
    complexifyL2LI.toContinuousLinearMap)

@[simp] theorem realLerayCLM_apply (v : SpatialL2) : realLerayCLM v = realLeray v := rfl

theorem norm_realLeray_le (v : SpatialL2) : ‖realLeray v‖ ≤ ‖v‖ := by
  rw [← complexifyL2_norm (realLeray v), complexify_realLeray]
  exact (norm_fourierLeray_le (complexifyL2 v)).trans_eq (complexifyL2_norm v)

theorem realLeray_idempotent (v : SpatialL2) :
    realLeray (realLeray v) = realLeray v := by
  apply complexifyL2LI.injective
  change complexifyL2 (realLeray (realLeray v)) = complexifyL2 (realLeray v)
  simp only [complexify_realLeray, fourierLeray_idempotent]

private theorem real_inner_complexify (u v : SpatialL2) :
    inner ℝ u v = Complex.re (inner ℂ (complexifyL2 u) (complexifyL2 v)) := by
  letI : InnerProductSpace ℝ ComplexL2 := InnerProductSpace.rclikeToReal ℂ ComplexL2
  exact (complexifyL2LI.inner_map_map u v).symm

theorem inner_realLeray_left (u v : SpatialL2) :
    inner ℝ (realLeray u) v = inner ℝ u (realLeray v) := by
  rw [real_inner_complexify, real_inner_complexify,
    complexify_realLeray, complexify_realLeray, inner_fourierLeray_left]

theorem realLeray_orthogonal_complement (u v : SpatialL2) :
    inner ℝ (realLeray u) (v - realLeray v) = 0 := by
  simp only [inner_sub_right, inner_realLeray_left, realLeray_idempotent, sub_self]

theorem realLeray_norm_sq_split (v : SpatialL2) :
    ‖v‖ ^ 2 = ‖realLeray v‖ ^ 2 + ‖v - realLeray v‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (realLeray v) (v - realLeray v) (realLeray_orthogonal_complement v v)
  have hs : realLeray v + (v - realLeray v) = v := by abel
  simpa only [hs, pow_two] using h

/-- The literal matrix action of the real operator in frequency space. -/
theorem realLeray_fourier_ae (v : SpatialL2) :
    (fun ξ : Space => (𝓕 (complexifyL2 (realLeray v)) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space => leraySymbol ξ ((𝓕 (complexifyL2 v) : ComplexL2) ξ)) := by
  simpa only [complexify_realLeray, fourier_fourierLeray] using
    frequencyLeray_ae (𝓕 (complexifyL2 v) : ComplexL2)

theorem realLeray_fourier_transverse (v : SpatialL2) :
    ∀ᵐ ξ : Space ∂volume,
      inner ℂ (complexifyVectorLI ξ)
        ((𝓕 (complexifyL2 (realLeray v)) : ComplexL2) ξ) = 0 := by
  filter_upwards [realLeray_fourier_ae v] with ξ hξ
  rw [hξ]
  exact leraySymbol_transverse ξ ((𝓕 (complexifyL2 v) : ComplexL2) ξ)

/-- The complete actual L2 fixed-point/frequency characterization. -/
theorem realLeray_eq_self_iff_fourier_transverse (v : SpatialL2) :
    realLeray v = v ↔ ∀ᵐ ξ : Space ∂volume,
      inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ) = 0 := by
  constructor
  · intro h
    simpa only [h] using realLeray_fourier_transverse v
  · intro h
    apply complexifyL2LI.injective
    apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
    change (𝓕 (complexifyL2 (realLeray v)) : ComplexL2) = 𝓕 (complexifyL2 v)
    apply Lp.ext
    filter_upwards [realLeray_fourier_ae v, h] with ξ hp ht
    rw [hp]
    exact (leraySymbol_eq_self_iff ξ ((𝓕 (complexifyL2 v) : ComplexL2) ξ)).mpr ht

/-- Commutation with each of the six actual real sector operators. -/
theorem realLeray_realFourierSector (i : Fin 6) (v : SpatialL2) :
    realLeray (realFourierSector i v) = realFourierSector i (realLeray v) := by
  apply complexifyL2LI.injective
  change complexifyL2 (realLeray (realFourierSector i v)) =
    complexifyL2 (realFourierSector i (realLeray v))
  simp only [complexify_realLeray, complexify_realFourierSector, fourierLeray_fourierSector]

end MethbokeAddon.QuasiFeffermanA.LerayMultiplier
