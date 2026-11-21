import MethbokeAddon.QuasiFeffermanA.LerayH1

/-!
# The exact native solenoidal range in full real L2

Compact solenoidal tests determine the actual tempered divergence without
assuming first derivatives in L2. Fourier differentiation and local test
separation then prove the frequency-transversality converse. This completes
the range of the previously constructed real Leray operator on all L2 inputs.
No H1 admission, pressure representative, or supplied preservation port occurs.

Prepared source requires matching external type and axiom evidence.
No local Lean, Lake, kernel audit or proof runner is used.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators ContDiff SchwartzMap LineDeriv FourierTransform

namespace MethbokeAddon.QuasiFeffermanA.LeraySolenoidal

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open QFA.Endpoints.Representation.CompactSchwartz
open LerayMultiplier LerayH1 PhysicalH1Divergence SixSectorNaturality RealSectorMultipliers

private theorem real_smul_complex (r : ℝ) (z : ComplexVector) :
    r • z = (r : ℂ) • z := by
  apply PiLp.ext
  intro j
  change r • z j = (r : ℂ) * z j
  exact Complex.real_smul

private theorem sum_slice_derivative_pairing
    (v : SpatialL2) (ψ : Space → ℝ) (hψ : ContDiff ℝ ∞ ψ)
    (hcompact : HasCompactSupport ψ) :
    (∑ j : Fin 3, coordinateSliceVectorCLM j
      (∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • v x)) =
        (∫ x : Space, inner ℝ (v x) (scalarGradient ψ x)) • coordinateVector 0 := by
  have hint (j : Fin 3) :
      Integrable (fun x : Space => fderiv ℝ ψ x (coordinateVector j) • v x) volume :=
    integrable_compact_test_smul v
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hcompact.fderiv_apply ℝ (coordinateVector j))
  calc
    (∑ j : Fin 3, coordinateSliceVectorCLM j
        (∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • v x)) =
        ∑ j : Fin 3, ∫ x : Space,
          coordinateSliceVectorCLM j (fderiv ℝ ψ x (coordinateVector j) • v x) := by
      apply Finset.sum_congr rfl
      intro j _
      exact ((coordinateSliceVectorCLM j).integral_comp_comm (hint j)).symm
    _ = ∫ x : Space, ∑ j : Fin 3,
        coordinateSliceVectorCLM j (fderiv ℝ ψ x (coordinateVector j) • v x) :=
      (integral_finsetSum Finset.univ
        (fun j _ => (coordinateSliceVectorCLM j).integrable_comp (hint j))).symm
    _ = ∫ x : Space, inner ℝ (v x) (scalarGradient ψ x) • coordinateVector 0 := by
      apply integral_congr_ae
      filter_upwards with x
      simp only [coordinateSliceVectorCLM_apply, PiLp.smul_apply, smul_eq_mul,
        ← Finset.sum_smul]
      congr 1
    _ = _ := integral_smul_const _ _

private theorem divergence_eq_zero_on_real_compact
    {v : SpatialL2} (hsol : Solenoidal v)
    (ψ : 𝓢(Space, ℝ)) (hcompact : HasCompactSupport (ψ : Space → ℝ)) :
    (∑ j : Fin 3, ∂_{coordinateVector j}
      (complexifyL2 (coordinateSliceL2 j v) : 𝓢'(Space, ComplexVector)))
        (ψ.postcompCLM Complex.ofRealCLM) = 0 := by
  have hψ : ContDiff ℝ ∞ (ψ : Space → ℝ) := ψ.smooth ⊤
  have heach (j : Fin 3) :
      (∂_{coordinateVector j}
        (complexifyL2 (coordinateSliceL2 j v) : 𝓢'(Space, ComplexVector)))
          (ψ.postcompCLM Complex.ofRealCLM) =
      -complexifyVectorCLM (coordinateSliceVectorCLM j
        (∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • v x)) := by
    rw [TemperedDistribution.lineDerivOp_apply_apply, map_neg,
      Lp.toTemperedDistribution_apply]
    apply congrArg Neg.neg
    calc
      (∫ x : Space, (∂_{coordinateVector j}
          (ψ.postcompCLM Complex.ofRealCLM)) x •
            complexifyL2 (coordinateSliceL2 j v) x) =
          ∫ x : Space, fderiv ℝ ψ x (coordinateVector j) •
            complexifyL2 (coordinateSliceL2 j v) x := by
        apply integral_congr_ae
        filter_upwards with x
        rw [H1Fourier.lineDeriv_postcomp_ofReal]
        exact (real_smul_complex (fderiv ℝ ψ x (coordinateVector j))
          (complexifyL2 (coordinateSliceL2 j v) x)).symm
      _ = complexifyVectorCLM
          (∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • coordinateSliceL2 j v x) :=
        integral_test_smul_complexifyL2 (coordinateSliceL2 j v) _
          (integrable_compact_test_smul (coordinateSliceL2 j v)
            ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
            (hcompact.fderiv_apply ℝ (coordinateVector j)))
      _ = _ := by
        congr 1
        have hpair := compactPairing_coordinateSlice j
          (fun x : Space => fderiv ℝ ψ x (coordinateVector j))
          ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
          (hcompact.fderiv_apply ℝ (coordinateVector j)) v
        simpa only [compactPairingCLM_apply] using hpair
  simp only [_root_.sum_apply, heach]
  calc
    (∑ j : Fin 3, -complexifyVectorCLM (coordinateSliceVectorCLM j
        (∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • v x))) =
        -complexifyVectorCLM (∑ j : Fin 3, coordinateSliceVectorCLM j
          (∫ x : Space, fderiv ℝ ψ x (coordinateVector j) • v x)) := by
      rw [Finset.sum_neg_distrib, map_sum]
    _ = 0 := by
      rw [sum_slice_derivative_pairing v ψ hψ hcompact,
        (hsol ψ hψ hcompact).2, zero_smul, map_zero, neg_zero]

private theorem divergence_distribution_eq_zero
    {v : SpatialL2} (hsol : Solenoidal v) :
    (∑ j : Fin 3, ∂_{coordinateVector j}
      (complexifyL2 (coordinateSliceL2 j v) : 𝓢'(Space, ComplexVector))) = 0 := by
  apply tempered_eq_of_eq_on_compactSchwartz denseCompactSchwartzTests
  intro φ hφ
  change HasCompactSupport (φ : Space → ℂ) at hφ
  let φr : 𝓢(Space, ℝ) := φ.postcompCLM Complex.reCLM
  let φi : 𝓢(Space, ℝ) := φ.postcompCLM Complex.imCLM
  have hr := divergence_eq_zero_on_real_compact hsol φr
    (hφ.comp_left (g := Complex.reCLM) (by rfl))
  have hi := divergence_eq_zero_on_real_compact hsol φi
    (hφ.comp_left (g := Complex.imCLM) (by rfl))
  have hsplit : φ = φr.postcompCLM Complex.ofRealCLM +
      Complex.I • φi.postcompCLM Complex.ofRealCLM := by
    apply SchwartzMap.ext
    intro x
    change φ x = ((φ x).re : ℂ) + Complex.I * ((φ x).im : ℂ)
    rw [mul_comm Complex.I]
    exact (Complex.re_add_im (φ x)).symm
  rw [hsplit]
  simp only [map_add, map_smul, hr, hi, smul_zero, add_zero, zero_apply]

private theorem ae_sum_multiplier_eq_zero
    (f : Fin 3 → ComplexL2) (m : Fin 3 → Space → ℝ)
    (hm_cont : ∀ j, Continuous (m j)) (hm_temp : ∀ j, (m j).HasTemperateGrowth)
    (hEq : (∑ j : Fin 3,
      TemperedDistribution.smulLeftCLM ComplexVector
        (fun x : Space => (m j x : ℂ)) (f j : 𝓢'(Space, ComplexVector))) = 0) :
    ∀ᵐ x : Space ∂volume, (∑ j : Fin 3, (m j x : ℂ) • f j x) = 0 := by
  have hlocal (j : Fin 3) :
      LocallyIntegrable (fun x : Space => (m j x : ℂ) • f j x) volume :=
    MeasureTheory.LocallyIntegrable.continuous_smul
      (Complex.continuous_ofReal.comp (hm_cont j))
      ((Lp.memLp (f j)).locallyIntegrable (by norm_num))
  apply ae_eq_of_integral_contDiff_smul_eq
    (locallyIntegrable_finsetSum Finset.univ (fun j _ => hlocal j))
    locallyIntegrable_zero
  intro g hg hcompact
  have hgC : HasCompactSupport (Complex.ofRealCLM ∘ g) := hcompact.comp_left rfl
  have hgCsmooth : ContDiff ℝ ∞ (Complex.ofRealCLM ∘ g) := by fun_prop
  let test : 𝓢(Space, ℂ) := hgC.toSchwartzMap hgCsmooth
  have htest (x : Space) : test x = (g x : ℂ) := rfl
  have hmC (j : Fin 3) : (fun x : Space => (m j x : ℂ)).HasTemperateGrowth := by
    simpa only [Function.comp_def, Complex.ofRealCLM_apply] using
      (Complex.ofRealCLM.hasTemperateGrowth.comp (hm_temp j))
  have heval (j : Fin 3) :
      (TemperedDistribution.smulLeftCLM ComplexVector
        (fun x : Space => (m j x : ℂ)) (f j : 𝓢'(Space, ComplexVector))) test =
      ∫ x : Space, ((m j x : ℂ) * (g x : ℂ)) • f j x := by
    simp only [TemperedDistribution.smulLeftCLM_apply_apply,
      Lp.toTemperedDistribution_apply,
      SchwartzMap.smulLeftCLM_apply_apply (hmC j), htest, smul_eq_mul]
  have hPair : (∑ j : Fin 3,
      ∫ x : Space, ((m j x : ℂ) * (g x : ℂ)) • f j x) = 0 := by
    have hEval := congrArg (fun T : 𝓢'(Space, ComplexVector) => T test) hEq
    simpa only [_root_.sum_apply, heval, zero_apply] using hEval
  have hint (j : Fin 3) :
      Integrable (fun x : Space => g x • ((m j x : ℂ) • f j x)) volume :=
    (hlocal j).integrable_smul_left_of_hasCompactSupport hg.continuous hcompact
  simp only [smul_zero, integral_zero]
  calc
    (∫ x : Space, g x • (∑ j : Fin 3, (m j x : ℂ) • f j x)) =
        ∫ x : Space, ∑ j : Fin 3, g x • ((m j x : ℂ) • f j x) := by
      simp only [Finset.smul_sum]
    _ = ∑ j : Fin 3, ∫ x : Space, g x • ((m j x : ℂ) • f j x) :=
      integral_finsetSum Finset.univ (fun j _ => hint j)
    _ = ∑ j : Fin 3, ∫ x : Space, ((m j x : ℂ) * (g x : ℂ)) • f j x := by
      apply Finset.sum_congr rfl
      intro j _
      apply integral_congr_ae
      filter_upwards with x
      rw [real_smul_complex, smul_smul, mul_comm]
    _ = 0 := hPair

/-- Native compact-test solenoidality implies frequency transversality for every
actual real L2 field, without a first-derivative membership premise. -/
theorem solenoidal_fourier_transverse
    {v : SpatialL2} (hsol : Solenoidal v) :
    ∀ᵐ ξ : Space ∂volume,
      inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ) = 0 := by
  have hρ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  have hF : (2 * (Real.pi : ℂ) * Complex.I) •
      (∑ j : Fin 3, TemperedDistribution.smulLeftCLM ComplexVector
        (fun ξ : Space => (inner ℝ ξ (coordinateVector j) : ℂ))
        ((𝓕 (complexifyL2 (coordinateSliceL2 j v)) : ComplexL2) :
          𝓢'(Space, ComplexVector))) = 0 := by
    calc
      _ = 𝓕 (∑ j : Fin 3, ∂_{coordinateVector j}
          (complexifyL2 (coordinateSliceL2 j v) : 𝓢'(Space, ComplexVector))) := by
        rw [Finset.smul_sum, fourier_sum]
        apply Finset.sum_congr rfl
        intro j _
        rw [TemperedDistribution.fourier_lineDerivOp_eq,
          Lp.fourier_toTemperedDistribution_eq]
      _ = 0 := by
        rw [divergence_distribution_eq_zero hsol, FourierTransform.fourier_zero]
  have hSum : (∑ j : Fin 3, TemperedDistribution.smulLeftCLM ComplexVector
      (fun ξ : Space => (inner ℝ ξ (coordinateVector j) : ℂ))
      ((𝓕 (complexifyL2 (coordinateSliceL2 j v)) : ComplexL2) :
        𝓢'(Space, ComplexVector))) = 0 := by
    let D : 𝓢'(Space, ComplexVector) :=
      ∑ j : Fin 3, TemperedDistribution.smulLeftCLM ComplexVector
        (fun ξ : Space => (inner ℝ ξ (coordinateVector j) : ℂ))
        ((𝓕 (complexifyL2 (coordinateSliceL2 j v)) : ComplexL2) :
          𝓢'(Space, ComplexVector))
    have hscaled : (2 * (Real.pi : ℂ) * Complex.I) • D =
        (0 : 𝓢'(Space, ComplexVector)) := hF
    change D = (0 : 𝓢'(Space, ComplexVector))
    apply UniformConvergenceCLM.ext
    intro ψ
    apply PiLp.ext
    intro k
    have hcoord := congrArg
      (fun T : 𝓢'(Space, ComplexVector) => (T ψ) k) hscaled
    change (2 * (Real.pi : ℂ) * Complex.I) * (D ψ) k = (0 : ℂ) at hcoord
    change (D ψ) k = (0 : ℂ)
    exact (mul_eq_zero.mp hcoord).resolve_left hρ
  have hfreq := ae_sum_multiplier_eq_zero
    (fun j : Fin 3 => (𝓕 (complexifyL2 (coordinateSliceL2 j v)) : ComplexL2))
    (fun j ξ => inner ℝ ξ (coordinateVector j))
    (fun _ => by fun_prop) (fun _ => by fun_prop) hSum
  have hcoords : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (𝓕 (complexifyL2 (coordinateSliceL2 j v)) : ComplexL2) ξ =
        complexCoordinateSliceVectorCLM j ((𝓕 (complexifyL2 v) : ComplexL2) ξ) := by
    apply ae_all_iff.mpr
    intro j
    rw [complexify_coordinateSliceL2, fourier_compLpL]
    exact (complexCoordinateSliceVectorCLM j).coeFn_compLpL
      (𝓕 (complexifyL2 v) : ComplexL2)
  filter_upwards [hfreq, hcoords] with ξ hzero hcoord
  have heq : (∑ j : Fin 3, (inner ℝ ξ (coordinateVector j) : ℂ) •
      (𝓕 (complexifyL2 (coordinateSliceL2 j v)) : ComplexL2) ξ) =
      inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ) •
        EuclideanSpace.single (0 : Fin 3) (1 : ℂ) := by
    rw [inner_complexifyVector_eq_sum, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro j _
    have hξ : inner ℝ ξ (coordinateVector j) = ξ j := by
      simpa only [coordinateVector, EuclideanSpace.basisFun_apply] using
        EuclideanSpace.inner_basisFun_real (Fin 3) ξ j
    rw [hcoord j, hξ, complexCoordinateSliceVectorCLM_apply, smul_smul]
  rw [heq] at hzero
  have hz := congrArg (fun z : ComplexVector => z (0 : Fin 3)) hzero
  simpa only [PiLp.smul_apply, PiLp.single_apply, if_pos rfl, ite_true, smul_eq_mul,
    mul_one, PiLp.zero_apply] using hz

/-- Exact all-L2 equivalence for the original compact-test predicate. -/
theorem solenoidal_iff_fourier_transverse (v : SpatialL2) :
    Solenoidal v ↔ ∀ᵐ ξ : Space ∂volume,
      inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ) = 0 := by
  constructor
  · exact solenoidal_fourier_transverse
  · intro h
    have hp := (realLeray_eq_self_iff_fourier_transverse v).mpr h
    simpa only [hp] using solenoidal_realLeray v

/-- The actual L2 Leray projection fixes precisely the native solenoidal fields. -/
theorem realLeray_eq_self_iff_solenoidal (v : SpatialL2) :
    realLeray v = v ↔ Solenoidal v :=
  (realLeray_eq_self_iff_fourier_transverse v).trans
    (solenoidal_iff_fourier_transverse v).symm

/-- Full native range characterization, with no H1 premise or assumed projector port. -/
theorem realLeray_range_iff_solenoidal (v : SpatialL2) :
    (∃ w : SpatialL2, realLeray w = v) ↔ Solenoidal v := by
  constructor
  · rintro ⟨w, rfl⟩
    exact solenoidal_realLeray w
  · intro hv
    exact ⟨v, (realLeray_eq_self_iff_solenoidal v).mpr hv⟩

/-- Actual six-sector solenoidal preservation now holds for all real L2 inputs. -/
theorem solenoidal_realFourierSector_L2 (i : Fin 6)
    {v : SpatialL2} (hsol : Solenoidal v) :
    Solenoidal (realFourierSector i v) := by
  apply (realLeray_eq_self_iff_solenoidal _).mp
  rw [realLeray_realFourierSector, (realLeray_eq_self_iff_solenoidal v).mpr hsol]

end MethbokeAddon.QuasiFeffermanA.LeraySolenoidal
