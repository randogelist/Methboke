import MethbokeAddon.QuasiFeffermanA.LerayMultiplier
import MethbokeAddon.QuasiFeffermanA.PhysicalH1SigmaSectors

/-!
# Leray transport on the original physical H1 and solenoidal graph

The actual supplied weak gradients commute with the constructed Leray map.
Coordinate Fourier naturality identifies the existing physical divergence
trace with the literal frequency contraction. This proves native solenoidality
and the exact fixed-point/range characterization on the original H1 graph.
No H2 premise, PDE solution, or supplied solenoidal-preservation port is used.

Every new declaration remains pending matching authorized external evidence.
No local Lean, Lake, kernel audit or proof runner is used.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ContDiff SchwartzMap

namespace MethbokeAddon.QuasiFeffermanA.LerayH1

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open LerayMultiplier PhysicalH1Divergence SixSectorNaturality RealSectorMultipliers

/-- Actual supplied first derivatives commute with the constructed real Leray operator. -/
theorem spatialWeakGradient_realLeray
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G) :
    SpatialWeakGradient (realLeray v) (fun j => realLeray (G j)) := by
  apply (H1Fourier.spatialWeakGradient_iff_fourier_ae _ _).mpr
  have hfreq := (H1Fourier.spatialWeakGradient_iff_fourier_ae v G).mp h
  apply ae_all_iff.mpr
  intro j
  have hp := frequencyLeray_multiplier_ae
    (𝓕 (complexifyL2 v) : ComplexL2) (𝓕 (complexifyL2 (G j)) : ComplexL2)
    (fun ξ : Space => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ (coordinateVector j) : ℂ))
    (ae_all_iff.mp hfreq j)
  change ∀ᵐ ξ : Space ∂volume,
    frequencyLeray (𝓕 (complexifyL2 (G j)) : ComplexL2) ξ =
      ((2 * Real.pi * Complex.I) * (inner ℝ ξ (coordinateVector j) : ℂ)) •
        frequencyLeray (𝓕 (complexifyL2 v) : ComplexL2) ξ at hp
  simpa only [complexify_realLeray, fourier_fourierLeray] using hp

/-- The actual L2 divergence trace has the literal first-order Fourier contraction. -/
theorem spatialGradientTrace_fourier_ae
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G) :
    (fun ξ : Space => (𝓕 (complexifyL2 (spatialGradientTrace G)) : ComplexL2) ξ) =ᵐ[volume]
      (fun ξ : Space =>
        ((2 * Real.pi * Complex.I) *
          inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ)) •
            EuclideanSpace.single (0 : Fin 3) (1 : ℂ)) := by
  have hF : (𝓕 (complexifyL2 (spatialGradientTrace G)) : ComplexL2) =
      ∑ j : Fin 3, (complexCoordinateSliceVectorCLM j).compLpL 2 volume
        (𝓕 (complexifyL2 (G j)) : ComplexL2) := by
    change 𝓕 (complexifyL2LI (∑ j : Fin 3, coordinateSliceL2 j (G j))) = _
    rw [map_sum]
    change 𝓕 (∑ j : Fin 3, complexifyL2 (coordinateSliceL2 j (G j))) = _
    rw [fourier_sum]
    simp only [complexify_coordinateSliceL2, fourier_compLpL]
  have hcoords : ∀ᵐ ξ : Space ∂volume, ∀ j : Fin 3,
      (complexCoordinateSliceVectorCLM j).compLpL 2 volume
        (𝓕 (complexifyL2 (G j)) : ComplexL2) ξ =
      complexCoordinateSliceVectorCLM j ((𝓕 (complexifyL2 (G j)) : ComplexL2) ξ) :=
    ae_all_iff.mpr (fun j => (complexCoordinateSliceVectorCLM j).coeFn_compLpL
      (𝓕 (complexifyL2 (G j)) : ComplexL2))
  rw [hF]
  filter_upwards [Lp.coeFn_fun_finsetSum Finset.univ
      (fun j : Fin 3 => (complexCoordinateSliceVectorCLM j).compLpL 2 volume
        (𝓕 (complexifyL2 (G j)) : ComplexL2)),
    hcoords, H1Fourier.spatialWeakGradient_fourier_ae h] with ξ hsum hc hg
  rw [hsum]
  calc
    (∑ j : Fin 3, (complexCoordinateSliceVectorCLM j).compLpL 2 volume
        (𝓕 (complexifyL2 (G j)) : ComplexL2) ξ) =
      ∑ j : Fin 3,
        ((2 * Real.pi * Complex.I) *
          ((ξ j : ℂ) * ((𝓕 (complexifyL2 v) : ComplexL2) ξ) j)) •
            EuclideanSpace.single (0 : Fin 3) (1 : ℂ) := by
      apply Finset.sum_congr rfl
      intro j _
      have hξ : inner ℝ ξ (coordinateVector j) = ξ j := by
        simpa only [coordinateVector, EuclideanSpace.basisFun_apply] using
          EuclideanSpace.inner_basisFun_real (Fin 3) ξ j
      rw [hc j, hg j, hξ]
      simp only [complexCoordinateSliceVectorCLM_apply, PiLp.smul_apply,
        smul_eq_mul, mul_assoc]
    _ = ((2 * Real.pi * Complex.I) *
        (∑ j : Fin 3, (ξ j : ℂ) * ((𝓕 (complexifyL2 v) : ComplexL2) ξ) j)) •
          EuclideanSpace.single (0 : Fin 3) (1 : ℂ) := by
      rw [Finset.mul_sum, Finset.sum_smul]
    _ = _ := by rw [inner_complexifyVector_eq_sum]

/-- Original compact-test solenoidality is equivalent to actual Fourier transversality
for a supplied physical first weak gradient; there is no H2 premise. -/
theorem spatialWeakGradient_solenoidal_iff_fourier_transverse
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G) :
    Solenoidal v ↔ ∀ᵐ ξ : Space ∂volume,
      inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ) = 0 := by
  rw [spatialWeakGradient_solenoidal_iff_trace_eq_zero h]
  have hρ : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 :=
    mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  constructor
  · intro hz
    have htrace := spatialGradientTrace_fourier_ae h
    have hFzero : (𝓕 (complexifyL2 (spatialGradientTrace G)) : ComplexL2) = 0 := by
      rw [hz, complexifyL2_zero]
      exact (Lp.fourierTransformₗᵢ Space ComplexVector).map_zero
    rw [hFzero] at htrace
    filter_upwards [htrace, Lp.coeFn_zero ComplexVector 2 (volume : Measure Space)]
      with ξ ht hzero
    rw [hzero] at ht
    have hcoord := congrArg (fun z : ComplexVector => z (0 : Fin 3)) ht
    have hprod : (2 * (Real.pi : ℂ) * Complex.I) *
        inner ℂ (complexifyVectorLI ξ) ((𝓕 (complexifyL2 v) : ComplexL2) ξ) = 0 := by
      simpa only [Pi.zero_apply, PiLp.zero_apply, PiLp.smul_apply, PiLp.single_apply,
        if_pos rfl, ite_true, smul_eq_mul, mul_one] using hcoord.symm
    exact (mul_eq_zero.mp hprod).resolve_left hρ
  · intro ht
    apply complexifyL2LI.injective
    change complexifyL2 (spatialGradientTrace G) = complexifyL2 (0 : SpatialL2)
    rw [complexifyL2_zero]
    apply (Lp.fourierTransformₗᵢ Space ComplexVector).injective
    change (𝓕 (complexifyL2 (spatialGradientTrace G)) : ComplexL2) = 𝓕 (0 : ComplexL2)
    rw [FourierTransform.fourier_zero]
    apply Lp.ext
    filter_upwards [spatialGradientTrace_fourier_ae h, ht,
      Lp.coeFn_zero ComplexVector 2 (volume : Measure Space)] with ξ htrace hξ hzero
    rw [htrace, hξ, mul_zero, zero_smul, hzero, Pi.zero_apply]

/-- Native solenoidality of the projected actual H1 field is a conclusion. -/
theorem solenoidal_realLeray_of_weakGradient
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G) :
    Solenoidal (realLeray v) :=
  (spatialWeakGradient_solenoidal_iff_fourier_transverse
    (spatialWeakGradient_realLeray h)).mpr (realLeray_fourier_transverse v)

/-- Every native solenoidal H1 velocity is fixed by the same actual L2 operator. -/
theorem realLeray_eq_self_of_solenoidal
    {v : SpatialL2} {G : Fin 3 → SpatialL2}
    (h : SpatialWeakGradient v G) (hs : Solenoidal v) : realLeray v = v :=
  (realLeray_eq_self_iff_fourier_transverse v).mpr
    ((spatialWeakGradient_solenoidal_iff_fourier_transverse h).mp hs)

/-- Every L2 input has native solenoidal Leray output, by actual Schwartz density
and continuity of every original compact-test functional. -/
theorem solenoidal_realLeray (v : SpatialL2) : Solenoidal (realLeray v) := by
  rw [solenoidal_iff_testCLM]
  intro φ
  let p : SpatialL2 → Prop := fun w => solenoidalTestCLM φ (realLeray w) = 0
  change p v
  apply DenseRange.induction_on (p := p)
    (SchwartzMap.denseRange_toLpCLM (E := Space) (F := Space)
      (p := 2) (μ := volume) ENNReal.ofNat_ne_top) v
  · apply isClosed_eq
    · exact (solenoidalTestCLM φ).continuous.comp realLerayCLM.continuous
    · exact continuous_const
  intro ψ
  exact (solenoidal_iff_testCLM (realLeray (ψ.toLp 2 volume))).mp
    (solenoidal_realLeray_of_weakGradient (schwartz_spatialWeakGradient ψ)) φ

/-- The actual Leray H1 graph element, with projected unique weak derivatives. -/
def physicalH1Leray (u : PhysicalH1) : PhysicalH1 :=
  physicalH1OfWeakGradient (realLeray (physicalH1Velocity u))
    (fun j => realLeray (physicalH1Gradient j u))
    (spatialWeakGradient_realLeray (physicalH1_weakGradient u))

@[simp] theorem physicalH1Leray_velocity (u : PhysicalH1) :
    physicalH1Velocity (physicalH1Leray u) = realLeray (physicalH1Velocity u) := rfl

@[simp] theorem physicalH1Leray_gradient (u : PhysicalH1) (j : Fin 3) :
    physicalH1Gradient j (physicalH1Leray u) = realLeray (physicalH1Gradient j u) := rfl

private theorem physicalH1Leray_add (u v : PhysicalH1) :
    physicalH1Leray (u + v) = physicalH1Leray u + physicalH1Leray v := by
  apply physicalH1Velocity_injective
  change realLerayCLM (physicalH1Velocity (u + v)) =
    physicalH1Velocity (physicalH1Leray u + physicalH1Leray v)
  simp only [map_add, realLerayCLM_apply, physicalH1Leray_velocity]

private theorem physicalH1Leray_smul (r : ℝ) (u : PhysicalH1) :
    physicalH1Leray (r • u) = r • physicalH1Leray u := by
  apply physicalH1Velocity_injective
  change realLerayCLM (physicalH1Velocity (r • u)) =
    physicalH1Velocity (r • physicalH1Leray u)
  simp only [map_smul, realLerayCLM_apply, physicalH1Leray_velocity]

theorem physicalH1Leray_norm_sq_le (u : PhysicalH1) :
    ‖physicalH1Leray u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [physicalH1_norm_sq, physicalH1_norm_sq]
  simp only [physicalH1Leray_velocity, physicalH1Leray_gradient]
  apply add_le_add
  · exact pow_le_pow_left₀ (norm_nonneg _) (norm_realLeray_le _) 2
  · exact Finset.sum_le_sum (fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_realLeray_le _) 2)

theorem norm_physicalH1Leray_le (u : PhysicalH1) : ‖physicalH1Leray u‖ ≤ ‖u‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (physicalH1Leray_norm_sq_le u)

/-- Bounded real-linear Leray projection on the original complete physical H1 graph. -/
def physicalH1LerayCLM : PhysicalH1 →L[ℝ] PhysicalH1 :=
  ({ toFun := physicalH1Leray
     map_add' := physicalH1Leray_add
     map_smul' := physicalH1Leray_smul } : PhysicalH1 →ₗ[ℝ] PhysicalH1).mkContinuous 1
    (fun u => by
      change ‖physicalH1Leray u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using norm_physicalH1Leray_le u)

@[simp] theorem physicalH1LerayCLM_apply (u : PhysicalH1) :
    physicalH1LerayCLM u = physicalH1Leray u := rfl

theorem physicalH1Leray_idempotent (u : PhysicalH1) :
    physicalH1Leray (physicalH1Leray u) = physicalH1Leray u := by
  apply physicalH1Velocity_injective
  simp only [physicalH1Leray_velocity, realLeray_idempotent]

theorem inner_physicalH1Leray_left (u v : PhysicalH1) :
    inner ℝ (physicalH1Leray u) v = inner ℝ u (physicalH1Leray v) := by
  simp only [physicalH1_inner_eq, physicalH1Leray_velocity,
    physicalH1Leray_gradient, inner_realLeray_left]

theorem physicalH1Leray_orthogonal_complement (u v : PhysicalH1) :
    inner ℝ (physicalH1Leray u) (v - physicalH1Leray v) = 0 := by
  simp only [inner_sub_right, inner_physicalH1Leray_left, physicalH1Leray_idempotent,
    sub_self]

theorem physicalH1Leray_norm_sq_split (u : PhysicalH1) :
    ‖u‖ ^ 2 = ‖physicalH1Leray u‖ ^ 2 + ‖u - physicalH1Leray u‖ ^ 2 := by
  have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero
    (physicalH1Leray u) (u - physicalH1Leray u)
    (physicalH1Leray_orthogonal_complement u u)
  have hs : physicalH1Leray u + (u - physicalH1Leray u) = u := by abel
  simpa only [hs, pow_two] using h

theorem physicalH1Leray_solenoidal (u : PhysicalH1) :
    Solenoidal (physicalH1Velocity (physicalH1Leray u)) :=
  solenoidal_realLeray (physicalH1Velocity u)

/-- Exact native H1 fixed-point criterion, retaining every compact solenoidal test. -/
theorem physicalH1Leray_eq_self_iff (u : PhysicalH1) :
    physicalH1Leray u = u ↔ Solenoidal (physicalH1Velocity u) := by
  constructor
  · intro h
    simpa only [h] using physicalH1Leray_solenoidal u
  · intro hs
    apply physicalH1Velocity_injective
    exact realLeray_eq_self_of_solenoidal (physicalH1_weakGradient u) hs

theorem physicalH1Leray_range_iff (u : PhysicalH1) :
    (∃ w : PhysicalH1, physicalH1Leray w = u) ↔ Solenoidal (physicalH1Velocity u) := by
  constructor
  · rintro ⟨w, rfl⟩
    exact physicalH1Leray_solenoidal w
  · intro hs
    exact ⟨u, (physicalH1Leray_eq_self_iff u).mpr hs⟩

/-- The output is constructed in the original closed solenoidal H1 graph. -/
def physicalH1SigmaLeray (u : PhysicalH1) : PhysicalH1Sigma :=
  ⟨(physicalH1Leray u).val,
    (mem_physicalH1SigmaGraph_iff _).mpr
      ⟨physicalH1_weakGradient (physicalH1Leray u), physicalH1Leray_solenoidal u⟩⟩

theorem physicalH1SigmaLeray_toH1 (u : PhysicalH1) :
    physicalH1SigmaToH1LI (physicalH1SigmaLeray u) = physicalH1Leray u := rfl

theorem physicalH1Leray_sigma_identity (u : PhysicalH1Sigma) :
    physicalH1Leray (physicalH1SigmaToH1LI u) = physicalH1SigmaToH1LI u :=
  (physicalH1Leray_eq_self_iff _).mpr (physicalH1Sigma_solenoidal u)

/-- Exact commutation with each of the six already constructed physical H1 sectors. -/
theorem physicalH1Leray_sector (i : Fin 6) (u : PhysicalH1) :
    physicalH1Leray (physicalH1Sector i u) = physicalH1Sector i (physicalH1Leray u) := by
  apply physicalH1Velocity_injective
  simp only [physicalH1Leray_velocity, physicalH1Sector_velocity,
    realLeray_realFourierSector]

end MethbokeAddon.QuasiFeffermanA.LerayH1
