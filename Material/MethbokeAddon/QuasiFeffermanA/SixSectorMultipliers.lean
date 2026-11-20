import MethbokeAddon.QuasiFeffermanA.SixSectors
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

/-!
# Actual complex-vector L2 sector multipliers and Fourier projections

The operators below act on the actual full-volume `Lp C3 2 volume` carrier.
They are constructed with `MemLp.indicator`, then conjugated by Mathlib's
L2 Fourier isometry. No supplied abstract projector or PDE premise is used.

The real inverse-Fourier range, native physical H1/solenoidal transport and
physical gradient-charge identities remain separate obligations. This source
is prepared for matching cached external compilation and named axiom audit;
no local Lean execution is authorized.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

namespace MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers

open QFA.Endpoints.Agmon

/-- Actual complex-vector L2 restriction to one of the six frequency cones. -/
def frequencySector (i : Fin 6) (f : ComplexL2) : ComplexL2 :=
  ((Lp.memLp f).indicator (measurableSet_sixSector i)).toLp
    ((sixSector i).indicator (fun ξ : Space => f ξ))

/-- The chosen L2 representative equals the literal vector indicator a.e. -/
theorem frequencySector_ae (i : Fin 6) (f : ComplexL2) :
    (fun ξ : Space => frequencySector i f ξ) =ᵐ[volume]
      (sixSector i).indicator (fun ξ : Space => f ξ) :=
  MemLp.coeFn_toLp _

/-- The actual sector restriction is norm-contractive. -/
theorem norm_frequencySector_le (i : Fin 6) (f : ComplexL2) :
    ‖frequencySector i f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [frequencySector_ae i f] with ξ hξ
  rw [hξ]
  by_cases h : ξ ∈ sixSector i <;> simp [h]

/-- Sector restriction is additive on L2 equivalence classes. -/
theorem frequencySector_add (i : Fin 6) (f g : ComplexL2) :
    frequencySector i (f + g) = frequencySector i f + frequencySector i g := by
  apply Lp.ext
  filter_upwards [frequencySector_ae i (f + g), frequencySector_ae i f,
    frequencySector_ae i g, Lp.coeFn_add f g,
    Lp.coeFn_add (frequencySector i f) (frequencySector i g)]
    with ξ hsum hf hg hadd htarget
  by_cases h : ξ ∈ sixSector i <;>
    simp [hsum, hf, hg, hadd, htarget, Set.indicator_apply, h]

/-- Sector restriction is homogeneous over the actual complex scalars. -/
theorem frequencySector_smul (i : Fin 6) (c : ℂ) (f : ComplexL2) :
    frequencySector i (c • f) = c • frequencySector i f := by
  apply Lp.ext
  filter_upwards [frequencySector_ae i (c • f), frequencySector_ae i f,
    Lp.coeFn_smul c f, Lp.coeFn_smul c (frequencySector i f)]
    with ξ hscaled hf hsource htarget
  by_cases h : ξ ∈ sixSector i <;>
    simp [hscaled, hf, hsource, htarget, Set.indicator_apply, h]

/-- The zero element is preserved without choosing a representative. -/
@[simp] theorem frequencySector_zero (i : Fin 6) : frequencySector i 0 = 0 := by
  have h := frequencySector_smul i (0 : ℂ) (0 : ComplexL2)
  simpa only [zero_smul] using h

/-- The constructed bounded complex-linear frequency projection. -/
def frequencySectorCLM (i : Fin 6) : ComplexL2 →L[ℂ] ComplexL2 :=
  ({ toFun := frequencySector i
     map_add' := frequencySector_add i
     map_smul' := frequencySector_smul i } : ComplexL2 →ₗ[ℂ] ComplexL2).mkContinuous 1
    (fun f => by simpa only [one_mul] using norm_frequencySector_le i f)

/-- Literal action of the packaged continuous linear map. -/
@[simp] theorem frequencySectorCLM_apply (i : Fin 6) (f : ComplexL2) :
    frequencySectorCLM i f = frequencySector i f := rfl

/-- Each actual frequency restriction is idempotent. -/
theorem frequencySector_idempotent (i : Fin 6) (f : ComplexL2) :
    frequencySector i (frequencySector i f) = frequencySector i f := by
  apply Lp.ext
  filter_upwards [frequencySector_ae i (frequencySector i f), frequencySector_ae i f]
    with ξ houter hinner
  by_cases h : ξ ∈ sixSector i <;>
    simp [houter, hinner, Set.indicator_apply, h]

/-- Distinct actual frequency restrictions annihilate each other. -/
theorem frequencySector_comp_eq_zero {i j : Fin 6} (hij : i ≠ j) (f : ComplexL2) :
    frequencySector i (frequencySector j f) = 0 := by
  apply Lp.ext
  filter_upwards [frequencySector_ae i (frequencySector j f), frequencySector_ae j f,
    Lp.coeFn_zero ComplexVector 2 (volume : Measure Space)] with ξ houter hinner hzero
  by_cases hi : ξ ∈ sixSector i
  · have hj : ξ ∉ sixSector j := by
      intro hj
      exact Set.disjoint_left.mp (sixSector_disjoint hij) hi hj
    simp [houter, hinner, hzero, Set.indicator_apply, hi, hj]
  · simp [houter, hzero, Set.indicator_apply, hi]

/-- Exact reconstruction as a finite sum of actual L2 classes. -/
theorem sum_frequencySector (f : ComplexL2) : ∑ i : Fin 6, frequencySector i f = f := by
  classical
  have hall : ∀ᵐ ξ : Space ∂volume, ∀ i : Fin 6,
      frequencySector i f ξ = (sixSector i).indicator (fun ξ : Space => f ξ) ξ :=
    ae_all_iff.mpr (fun i => frequencySector_ae i f)
  apply Lp.ext
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ (fun i : Fin 6 => frequencySector i f),
    hall] with ξ hsum hsector
  rw [hsum]
  simp_rw [hsector]
  obtain ⟨i, hi, hunique⟩ := existsUnique_mem_sixSector ξ
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    have hj : ξ ∉ sixSector j := fun hj => hji (hunique j hj)
    simp [hj]
  · intro hi_not
    exact (hi_not (Finset.mem_univ i)).elim

/-- Self-adjointness for the actual complex-vector L2 inner product. -/
theorem inner_frequencySector_left (i : Fin 6) (f g : ComplexL2) :
    inner ℂ (frequencySector i f) g = inner ℂ f (frequencySector i g) := by
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [frequencySector_ae i f, frequencySector_ae i g] with ξ hf hg
  by_cases h : ξ ∈ sixSector i <;> simp [hf, hg, Set.indicator_apply, h]

/-- Different actual frequency sectors are orthogonal for arbitrary inputs. -/
theorem inner_frequencySector_eq_zero {i j : Fin 6} (hij : i ≠ j) (f g : ComplexL2) :
    inner ℂ (frequencySector i f) (frequencySector j g) = 0 := by
  rw [inner_frequencySector_left, frequencySector_comp_eq_zero hij]
  simp

/-- Exact squared-norm decomposition of the full complex-vector L2 field. -/
theorem sum_norm_frequencySector_sq (f : ComplexL2) :
    (∑ i : Fin 6, ‖frequencySector i f‖ ^ 2) = ‖f‖ ^ 2 := by
  calc
    (∑ i : Fin 6, ‖frequencySector i f‖ ^ 2) =
        ∑ i : Fin 6, Complex.re (inner ℂ f (frequencySector i f)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_sq_eq_re_inner (𝕜 := ℂ), inner_frequencySector_left,
        frequencySector_idempotent]
    _ = Complex.re (∑ i : Fin 6, inner ℂ f (frequencySector i f)) := by
      exact (map_sum Complex.reCLM _ _).symm
    _ = Complex.re (inner ℂ f f) := by rw [← inner_sum, sum_frequencySector]
    _ = ‖f‖ ^ 2 := (norm_sq_eq_re_inner (𝕜 := ℂ) f).symm

/-- The concrete inverse-Fourier conjugate, on the complex-vector L2 carrier. -/
def fourierSector (i : Fin 6) (f : ComplexL2) : ComplexL2 :=
  𝓕⁻ (frequencySector i (𝓕 f))

/-- The frequency action of the actual Fourier-conjugate operator. -/
@[simp] theorem fourier_fourierSector (i : Fin 6) (f : ComplexL2) :
    𝓕 (fourierSector i f) = frequencySector i (𝓕 f) :=
  fourier_fourierInv_eq _

/-- The Fourier-conjugate projection is norm-contractive by Plancherel. -/
theorem norm_fourierSector_le (i : Fin 6) (f : ComplexL2) :
    ‖fourierSector i f‖ ≤ ‖f‖ := by
  rw [← Lp.norm_fourier_eq (fourierSector i f), fourier_fourierSector]
  exact (norm_frequencySector_le i (𝓕 f)).trans_eq (Lp.norm_fourier_eq f)

/-- Complex-linear additivity survives Fourier conjugation. -/
theorem fourierSector_add (i : Fin 6) (f g : ComplexL2) :
    fourierSector i (f + g) = fourierSector i f + fourierSector i g := by
  simp only [fourierSector, fourier_add, frequencySector_add, fourierInv_add]

/-- Complex homogeneity survives Fourier conjugation. -/
theorem fourierSector_smul (i : Fin 6) (c : ℂ) (f : ComplexL2) :
    fourierSector i (c • f) = c • fourierSector i f := by
  simp only [fourierSector, fourier_smul, frequencySector_smul, fourierInv_smul]

/-- The constructed bounded complex-linear Fourier projection. -/
def fourierSectorCLM (i : Fin 6) : ComplexL2 →L[ℂ] ComplexL2 :=
  ({ toFun := fourierSector i
     map_add' := fourierSector_add i
     map_smul' := fourierSector_smul i } : ComplexL2 →ₗ[ℂ] ComplexL2).mkContinuous 1
    (fun f => by simpa only [one_mul] using norm_fourierSector_le i f)

/-- Literal action of the Fourier projection continuous linear map. -/
@[simp] theorem fourierSectorCLM_apply (i : Fin 6) (f : ComplexL2) :
    fourierSectorCLM i f = fourierSector i f := rfl

/-- Actual idempotence after Fourier conjugation. -/
theorem fourierSector_idempotent (i : Fin 6) (f : ComplexL2) :
    fourierSector i (fourierSector i f) = fourierSector i f := by
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  change 𝓕 (fourierSector i (fourierSector i f)) = 𝓕 (fourierSector i f)
  simp only [fourier_fourierSector, frequencySector_idempotent]

/-- Distinct actual Fourier projections annihilate each other. -/
theorem fourierSector_comp_eq_zero {i j : Fin 6} (hij : i ≠ j) (f : ComplexL2) :
    fourierSector i (fourierSector j f) = 0 := by
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  change 𝓕 (fourierSector i (fourierSector j f)) = 𝓕 (0 : ComplexL2)
  simp only [fourier_fourierSector, frequencySector_comp_eq_zero hij, fourier_zero]

/-- Reconstruction by the six actual Fourier projections. -/
theorem sum_fourierSector (f : ComplexL2) : ∑ i : Fin 6, fourierSector i f = f := by
  apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
  change 𝓕 (∑ i : Fin 6, fourierSector i f) = 𝓕 f
  rw [fourier_sum]
  simp only [fourier_fourierSector]
  exact sum_frequencySector (𝓕 f)

/-- Self-adjointness transported by the actual L2 Fourier isometry. -/
theorem inner_fourierSector_left (i : Fin 6) (f g : ComplexL2) :
    inner ℂ (fourierSector i f) g = inner ℂ f (fourierSector i g) := by
  rw [← Lp.inner_fourier_eq (fourierSector i f) g,
    ← Lp.inner_fourier_eq f (fourierSector i g)]
  simp only [fourier_fourierSector]
  exact inner_frequencySector_left i (𝓕 f) (𝓕 g)

/-- Exact orthogonality for the six Fourier-conjugate projections. -/
theorem inner_fourierSector_eq_zero {i j : Fin 6} (hij : i ≠ j) (f g : ComplexL2) :
    inner ℂ (fourierSector i f) (fourierSector j g) = 0 := by
  rw [← Lp.inner_fourier_eq (fourierSector i f) (fourierSector j g)]
  simp only [fourier_fourierSector]
  exact inner_frequencySector_eq_zero hij (𝓕 f) (𝓕 g)

/-- Exact squared-norm decomposition after Fourier conjugation. -/
theorem sum_norm_fourierSector_sq (f : ComplexL2) :
    (∑ i : Fin 6, ‖fourierSector i f‖ ^ 2) = ‖f‖ ^ 2 := by
  have hnorm (i : Fin 6) : ‖fourierSector i f‖ = ‖frequencySector i (𝓕 f)‖ := by
    rw [← Lp.norm_fourier_eq (fourierSector i f), fourier_fourierSector]
  simp only [hnorm, sum_norm_frequencySector_sq, Lp.norm_fourier_eq]

/-- Restriction commutes with a supplied a.e. scalar multiplier identity.
The two actual L2 witnesses are explicit; no weighted-L2 witness is invented. -/
theorem frequencySector_multiplier_ae (i : Fin 6) (f g : ComplexL2) (m : Space → ℂ)
    (h : (fun ξ : Space => g ξ) =ᵐ[volume] (fun ξ : Space => m ξ • f ξ)) :
    (fun ξ : Space => frequencySector i g ξ) =ᵐ[volume]
      (fun ξ : Space => m ξ • frequencySector i f ξ) := by
  filter_upwards [frequencySector_ae i g, frequencySector_ae i f, h] with ξ hg hf hgf
  by_cases hξ : ξ ∈ sixSector i <;> simp [hg, hf, hgf, Set.indicator_apply, hξ]

end MethbokeAddon.QuasiFeffermanA.SixSectorMultipliers
