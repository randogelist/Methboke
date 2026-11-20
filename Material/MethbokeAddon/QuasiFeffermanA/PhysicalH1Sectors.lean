import MethbokeAddon.QuasiFeffermanA.RealSectorMultipliers
import MethbokeAddon.QuasiFeffermanA.H1FourierReverse
import MethbokeAddon.QuasiFeffermanA.H1Spectral
import MethbokeAddon.QuasiFeffermanA.SixChargeBudget

/-!
# Actual six Fourier projections on the physical H1 graph

Projecting the supplied real L2 gradient components gives the actual weak
gradient of each projected velocity, by the accepted two-way Fourier bridge.
This constructs bounded real-linear projections on the full native H1 graph.
Their physical gradient charges are nonnegative, continuous and exactly
additive, with the Fourier normalization 4*pi^2 retained.

The full stopped-budget comparisons preserve infinite values. No endpoint
extension, universal budget finiteness, PDE evolution or solenoidal-preservation
premise is introduced. The native solenoidal restriction is a separate edge.

Prepared source requires matching cached external compilation and named audits.
No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform ENNReal

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open RealSectorMultipliers SixSectorMultipliers

/-- Projecting the supplied real L2 weak gradients constructs the actual
weak gradients of the projected velocity. No higher derivative is required. -/
theorem spatialWeakGradient_realFourierSector (i : Fin 6)
    {v : SpatialL2} {G : Fin 3 → SpatialL2} (h : SpatialWeakGradient v G) :
    SpatialWeakGradient (realFourierSector i v) (fun j => realFourierSector i (G j)) := by
  apply (H1Fourier.spatialWeakGradient_iff_fourier_ae _ _).mpr
  have hfreq := (H1Fourier.spatialWeakGradient_iff_fourier_ae v G).mp h
  apply ae_all_iff.mpr
  intro j
  have hp := frequencySector_multiplier_ae i
    (𝓕 (complexifyL2 v) : ComplexL2) (𝓕 (complexifyL2 (G j)) : ComplexL2)
    (fun ξ : Space => (2 * Real.pi * Complex.I) *
      (inner ℝ ξ (coordinateVector j) : ℂ))
    (ae_all_iff.mp hfreq j)
  simpa only [complexify_realFourierSector, fourier_fourierSector] using hp

/-- The physical H1 sector element uses the actual projected velocity and
the actual projections of its supplied weak-gradient fields. -/
def physicalH1Sector (i : Fin 6) (u : PhysicalH1) : PhysicalH1 :=
  physicalH1OfWeakGradient (realFourierSector i (physicalH1Velocity u))
    (fun j => realFourierSector i (physicalH1Gradient j u))
    (spatialWeakGradient_realFourierSector i (physicalH1_weakGradient u))

@[simp] theorem physicalH1Sector_velocity (i : Fin 6) (u : PhysicalH1) :
    physicalH1Velocity (physicalH1Sector i u) =
      realFourierSector i (physicalH1Velocity u) := rfl

/-- Literal commutation of the native physical weak-gradient map and the
constructed real Fourier sector projection. -/
@[simp] theorem physicalH1Sector_gradient (i : Fin 6) (u : PhysicalH1) (j : Fin 3) :
    physicalH1Gradient j (physicalH1Sector i u) =
      realFourierSector i (physicalH1Gradient j u) := rfl

theorem physicalH1Sector_add (i : Fin 6) (u v : PhysicalH1) :
    physicalH1Sector i (u + v) = physicalH1Sector i u + physicalH1Sector i v := by
  apply physicalH1Velocity_injective
  simp only [physicalH1Sector_velocity, map_add, realFourierSector_add]

theorem physicalH1Sector_smul (i : Fin 6) (r : ℝ) (u : PhysicalH1) :
    physicalH1Sector i (r • u) = r • physicalH1Sector i u := by
  apply physicalH1Velocity_injective
  simp only [physicalH1Sector_velocity, map_smul, realFourierSector_smul]

@[simp] theorem physicalH1Sector_zero (i : Fin 6) : physicalH1Sector i 0 = 0 := by
  apply physicalH1Velocity_injective
  simp only [physicalH1Sector_velocity, map_zero, realFourierSector_zero]

/-- The exact inhomogeneous H1 norm contracts, including its velocity term. -/
theorem physicalH1Sector_norm_sq_le (i : Fin 6) (u : PhysicalH1) :
    ‖physicalH1Sector i u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [physicalH1_norm_sq, physicalH1_norm_sq]
  simp only [physicalH1Sector_velocity, physicalH1Sector_gradient]
  apply add_le_add
  · exact pow_le_pow_left₀ (norm_nonneg _) (norm_realFourierSector_le i _) 2
  · exact Finset.sum_le_sum (fun j _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_realFourierSector_le i _) 2)

theorem norm_physicalH1Sector_le (i : Fin 6) (u : PhysicalH1) :
    ‖physicalH1Sector i u‖ ≤ ‖u‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (physicalH1Sector_norm_sq_le i u)

/-- The constructed bounded real-linear projection on the actual H1 graph. -/
def physicalH1SectorCLM (i : Fin 6) : PhysicalH1 →L[ℝ] PhysicalH1 :=
  ({ toFun := physicalH1Sector i
     map_add' := physicalH1Sector_add i
     map_smul' := physicalH1Sector_smul i } : PhysicalH1 →ₗ[ℝ] PhysicalH1).mkContinuous 1
    (fun u => by
      change ‖physicalH1Sector i u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using norm_physicalH1Sector_le i u)

@[simp] theorem physicalH1SectorCLM_apply (i : Fin 6) (u : PhysicalH1) :
    physicalH1SectorCLM i u = physicalH1Sector i u := rfl

theorem physicalH1Sector_idempotent (i : Fin 6) (u : PhysicalH1) :
    physicalH1Sector i (physicalH1Sector i u) = physicalH1Sector i u := by
  apply physicalH1Velocity_injective
  simp only [physicalH1Sector_velocity, realFourierSector_idempotent]

theorem physicalH1Sector_comp_eq_zero {i k : Fin 6} (hik : i ≠ k) (u : PhysicalH1) :
    physicalH1Sector i (physicalH1Sector k u) = 0 := by
  apply physicalH1Velocity_injective
  simp only [physicalH1Sector_velocity, realFourierSector_comp_eq_zero hik, map_zero]

/-- Reconstruction holds on the native graph, rather than only on L2 velocities. -/
theorem sum_physicalH1Sector (u : PhysicalH1) :
    (∑ i : Fin 6, physicalH1Sector i u) = u := by
  apply physicalH1Velocity_injective
  simp only [map_sum, physicalH1Sector_velocity, sum_realFourierSector]

/-- The inherited native H1 inner product is its actual componentwise L2 sum. -/
theorem physicalH1_inner_eq (u v : PhysicalH1) :
    inner ℝ u v = inner ℝ (physicalH1Velocity u) (physicalH1Velocity v) +
      ∑ j : Fin 3, inner ℝ (physicalH1Gradient j u) (physicalH1Gradient j v) := by
  change inner ℝ u.val v.val = inner ℝ (u.val 0) (v.val 0) +
    ∑ j : Fin 3, inner ℝ (u.val j.succ) (v.val j.succ)
  rw [PiLp.inner_apply, Fin.sum_univ_succ]

theorem inner_physicalH1Sector_left (i : Fin 6) (u v : PhysicalH1) :
    inner ℝ (physicalH1Sector i u) v = inner ℝ u (physicalH1Sector i v) := by
  simp only [physicalH1_inner_eq, physicalH1Sector_velocity, physicalH1Sector_gradient,
    inner_realFourierSector_left]

theorem inner_physicalH1Sector_eq_zero {i k : Fin 6} (hik : i ≠ k)
    (u v : PhysicalH1) :
    inner ℝ (physicalH1Sector i u) (physicalH1Sector k v) = 0 := by
  simp only [physicalH1_inner_eq, physicalH1Sector_velocity, physicalH1Sector_gradient,
    inner_realFourierSector_eq_zero hik, Finset.sum_const_zero, add_zero]

/-- Exact Pythagorean splitting retains the full inhomogeneous H1 norm. -/
theorem sum_norm_physicalH1Sector_sq (u : PhysicalH1) :
    (∑ i : Fin 6, ‖physicalH1Sector i u‖ ^ 2) = ‖u‖ ^ 2 := by
  simp_rw [physicalH1_norm_sq, physicalH1Sector_velocity, physicalH1Sector_gradient]
  rw [Finset.sum_add_distrib, sum_norm_realFourierSector_sq, Finset.sum_comm]
  simp_rw [sum_norm_realFourierSector_sq]

theorem physicalH1Enstrophy_sector (i : Fin 6) (u : PhysicalH1) :
    physicalH1Enstrophy (physicalH1Sector i u) =
      ∑ j : Fin 3, ‖realFourierSector i (physicalH1Gradient j u)‖ ^ 2 := rfl

/-- Gradient charges split independently of the velocity-energy term. -/
theorem sum_physicalH1Enstrophy_sector (u : PhysicalH1) :
    (∑ i : Fin 6, physicalH1Enstrophy (physicalH1Sector i u)) =
      physicalH1Enstrophy u := by
  simp_rw [physicalH1Enstrophy_sector]
  rw [Finset.sum_comm]
  simp only [sum_norm_realFourierSector_sq, physicalH1Enstrophy]

/-- The physical sector charge is the squared norm of its actual weak gradient. -/
def physicalH1SectorCharge (i : Fin 6) (u : PhysicalH1) : ℝ :=
  physicalH1Enstrophy (physicalH1Sector i u)

theorem physicalH1SectorCharge_eq (i : Fin 6) (u : PhysicalH1) :
    physicalH1SectorCharge i u =
      ∑ j : Fin 3, ‖realFourierSector i (physicalH1Gradient j u)‖ ^ 2 := rfl

theorem physicalH1SectorCharge_nonneg (i : Fin 6) (u : PhysicalH1) :
    0 ≤ physicalH1SectorCharge i u :=
  physicalH1Enstrophy_nonneg (physicalH1Sector i u)

theorem sum_physicalH1SectorCharge (u : PhysicalH1) :
    (∑ i : Fin 6, physicalH1SectorCharge i u) = physicalH1Enstrophy u :=
  sum_physicalH1Enstrophy_sector u

theorem physicalH1SectorCharge_continuous (i : Fin 6) :
    Continuous (physicalH1SectorCharge i) :=
  physicalH1Enstrophy_continuous.comp (physicalH1SectorCLM i).continuous

/-- Charges inherit continuity on exactly the supplied existing time set. -/
theorem physicalH1SectorCharge_continuousOn (i : Fin 6) (U : ℝ → PhysicalH1)
    {s : Set ℝ} (hU : ContinuousOn U s) :
    ContinuousOn (fun t => physicalH1SectorCharge i (U t)) s :=
  (physicalH1SectorCharge_continuous i).comp_continuousOn hU

/-- Genuine weighted Fourier integrability follows from the constructed H1
gradient, with no Laplacian or separate spectral-admission premise. -/
theorem physicalH1Sector_fourier_weighted_integrable (i : Fin 6) (u : PhysicalH1) :
    Integrable (fun ξ : Space => ‖ξ‖ ^ 2 *
      ‖(𝓕 (complexifyL2 (physicalH1Velocity (physicalH1Sector i u))) : ComplexL2) ξ‖ ^ 2)
      volume :=
  H1Spectral.physicalH1_fourier_enstrophy_integrable (physicalH1Sector i u)

theorem physicalH1SectorCharge_eq_fourier (i : Fin 6) (u : PhysicalH1) :
    physicalH1SectorCharge i u = (4 * Real.pi ^ 2) *
      (∫ ξ : Space, ‖ξ‖ ^ 2 *
        ‖(𝓕 (complexifyL2 (physicalH1Velocity (physicalH1Sector i u))) : ComplexL2) ξ‖ ^ 2) :=
  H1Spectral.physicalH1_enstrophy_eq_fourier (physicalH1Sector i u)

/-- The actual physical charge is the literal registered sector integral,
with the physical Fourier normalization retained. -/
theorem physicalH1SectorCharge_eq_sector_integral (i : Fin 6) (u : PhysicalH1) :
    physicalH1SectorCharge i u = (4 * Real.pi ^ 2) *
      (∫ ξ : Space in sixSector i, ‖ξ‖ ^ 2 *
        ‖(𝓕 (complexifyL2 (physicalH1Velocity u)) : ComplexL2) ξ‖ ^ 2) := by
  rw [physicalH1SectorCharge_eq_fourier, physicalH1Sector_velocity,
    complexify_realFourierSector, fourier_fourierSector]
  congr 1
  rw [← integral_indicator (measurableSet_sixSector i)]
  apply integral_congr_ae
  filter_upwards [frequencySector_ae i (𝓕 (complexifyL2 (physicalH1Velocity u)))]
    with ξ hξ
  rw [hξ]
  by_cases h : ξ ∈ sixSector i <;> simp [h]

/-- The original physical pointwise factor-six comparison follows from the
constructed nonnegative charges and their exact sum identity. -/
theorem physicalH1Sector_charge_sq_bounds (u : PhysicalH1) :
    (∑ i : Fin 6, (physicalH1SectorCharge i u) ^ 2) ≤ (physicalH1Enstrophy u) ^ 2 ∧
      (physicalH1Enstrophy u) ^ 2 ≤ 6 * ∑ i : Fin 6, (physicalH1SectorCharge i u) ^ 2 := by
  constructor
  · simpa only [sum_physicalH1SectorCharge] using
      six_charge_sum_sq_le_sq_sum (fun i => physicalH1SectorCharge i u)
        (fun i => physicalH1SectorCharge_nonneg i u)
  · simpa only [sum_physicalH1SectorCharge] using
      six_charge_sq_sum_le_six_sum_sq (fun i => physicalH1SectorCharge i u)

/-- Full ENNReal budget comparison now uses constructed physical charges;
nonnegativity and charge additivity are conclusions, not supplied premises. -/
theorem physicalH1Sector_budget_bounds (U : ℝ → PhysicalH1) (b : ℝ) :
    sixChargeBudget (fun i t => physicalH1SectorCharge i (U t))
        (volume.restrict (Ioo (0 : ℝ) b)) ≤
      stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b ∧
    stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b ≤
      6 * sixChargeBudget (fun i t => physicalH1SectorCharge i (U t))
        (volume.restrict (Ioo (0 : ℝ) b)) :=
  stoppedSquareBudget_six_charge_bounds _ _ b
    (Filter.Eventually.of_forall (fun t i => physicalH1SectorCharge_nonneg i (U t)))
    (Filter.Eventually.of_forall (fun t => (sum_physicalH1SectorCharge (U t)).symm))

theorem physicalH1Sector_budget_finite_iff (U : ℝ → PhysicalH1) (b : ℝ) :
    stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b ≠ ∞ ↔
      sixChargeBudget (fun i t => physicalH1SectorCharge i (U t))
        (volume.restrict (Ioo (0 : ℝ) b)) ≠ ∞ :=
  stoppedSquareBudget_finite_iff_six_charge _ _ b
    (Filter.Eventually.of_forall (fun t i => physicalH1SectorCharge_nonneg i (U t)))
    (Filter.Eventually.of_forall (fun t => (sum_physicalH1SectorCharge (U t)).symm))

/-- Continuity on the open lifetime suffices for exact full-budget splitting;
it asserts no finite maximal-time extension and no finiteness of the values. -/
theorem physicalH1Sector_budget_eq_sum (U : ℝ → PhysicalH1) (b : ℝ)
    (hU : ContinuousOn U (Ioo (0 : ℝ) b)) :
    sixChargeBudget (fun i t => physicalH1SectorCharge i (U t))
        (volume.restrict (Ioo (0 : ℝ) b)) =
      ∑ i : Fin 6, ∫⁻ t in Ioo (0 : ℝ) b,
        ENNReal.ofReal ((physicalH1SectorCharge i (U t)) ^ 2) :=
  sixChargeBudget_eq_sum_of_aemeasurable _ _
    (fun i => (physicalH1SectorCharge_continuousOn i U hU).aemeasurable measurableSet_Ioo)

theorem physicalH1Sector_budget_finite_iff_each (U : ℝ → PhysicalH1) (b : ℝ)
    (hU : ContinuousOn U (Ioo (0 : ℝ) b)) :
    stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b ≠ ∞ ↔
      ∀ i : Fin 6, (∫⁻ t in Ioo (0 : ℝ) b,
        ENNReal.ofReal ((physicalH1SectorCharge i (U t)) ^ 2)) ≠ ∞ :=
  (physicalH1Sector_budget_finite_iff U b).trans
    (sixChargeBudget_finite_iff_each _ _
      (fun i => (physicalH1SectorCharge_continuousOn i U hU).aemeasurable measurableSet_Ioo))

end MethbokeAddon.QuasiFeffermanA
