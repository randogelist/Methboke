import MethbokeAddon.QuasiFeffermanA.SixSectorNaturality

/-!
# Actual six Fourier projections on solenoidal physical H1

The native compact-test divergence criterion and proved coordinate naturality
establish solenoidal preservation before each projected graph element is
constructed. The inclusion into full physical H1 is an actual real-linear
isometry, so the previously constructed H1 projection algebra and physical
charge identities transfer to the same solenoidal carrier.

No assumed projector record, divergence-preservation premise, higher derivative,
physical PDE evolution or temporal continuation is introduced. Matching cached
external compilation and complete named audits remain required.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory FourierTransform
open scoped BigOperators FourierTransform

namespace MethbokeAddon.QuasiFeffermanA

open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open RealSectorMultipliers SixSectorNaturality

/-- Inclusion of the actual closed solenoidal graph into the same physical H1
graph preserves its complete inhomogeneous Hilbert norm exactly. -/
def physicalH1SigmaToH1LI : PhysicalH1Sigma →ₗᵢ[ℝ] PhysicalH1 where
  toFun u := ⟨u.val, (mem_physicalH1Graph_iff u.val).mpr
    (physicalH1Sigma_weakGradient u)⟩
  map_add' u v := rfl
  map_smul' r u := rfl
  norm_map' u := rfl

@[simp] theorem physicalH1SigmaToH1LI_val (u : PhysicalH1Sigma) :
    (physicalH1SigmaToH1LI u).val = u.val := rfl

@[simp] theorem physicalH1SigmaToH1LI_velocity (u : PhysicalH1Sigma) :
    physicalH1Velocity (physicalH1SigmaToH1LI u) = u.val 0 := rfl

@[simp] theorem physicalH1SigmaToH1LI_gradient (u : PhysicalH1Sigma) (j : Fin 3) :
    physicalH1Gradient j (physicalH1SigmaToH1LI u) = u.val j.succ := rfl

/-- The actual projected velocity and gradients satisfy both native graph
conditions, including every compact solenoidal test. -/
def physicalH1SigmaSector (i : Fin 6) (u : PhysicalH1Sigma) : PhysicalH1Sigma :=
  ⟨h1Pack (realFourierSector i (u.val 0))
      (fun j => realFourierSector i (u.val j.succ)),
    (mem_physicalH1SigmaGraph_iff _).mpr
      ⟨spatialWeakGradient_realFourierSector i (physicalH1Sigma_weakGradient u),
        solenoidal_realFourierSector i (physicalH1Sigma_weakGradient u)
          (physicalH1Sigma_solenoidal u)⟩⟩

@[simp] theorem physicalH1SigmaSector_velocity (i : Fin 6) (u : PhysicalH1Sigma) :
    (physicalH1SigmaSector i u).val 0 = realFourierSector i (u.val 0) := rfl

@[simp] theorem physicalH1SigmaSector_gradient (i : Fin 6) (u : PhysicalH1Sigma)
    (j : Fin 3) :
    (physicalH1SigmaSector i u).val j.succ = realFourierSector i (u.val j.succ) := rfl

/-- The restricted projection is literally the previously constructed full H1
projection under the native isometric inclusion. -/
theorem physicalH1SigmaSector_toH1 (i : Fin 6) (u : PhysicalH1Sigma) :
    physicalH1SigmaToH1LI (physicalH1SigmaSector i u) =
      physicalH1Sector i (physicalH1SigmaToH1LI u) := by
  apply physicalH1Velocity_injective
  rfl

theorem physicalH1SigmaSector_add (i : Fin 6) (u v : PhysicalH1Sigma) :
    physicalH1SigmaSector i (u + v) =
      physicalH1SigmaSector i u + physicalH1SigmaSector i v := by
  apply physicalH1SigmaToH1LI.injective
  simp only [physicalH1SigmaSector_toH1, map_add, physicalH1Sector_add]

theorem physicalH1SigmaSector_smul (i : Fin 6) (r : ℝ) (u : PhysicalH1Sigma) :
    physicalH1SigmaSector i (r • u) = r • physicalH1SigmaSector i u := by
  apply physicalH1SigmaToH1LI.injective
  simp only [physicalH1SigmaSector_toH1, map_smul, physicalH1Sector_smul]

@[simp] theorem physicalH1SigmaSector_zero (i : Fin 6) :
    physicalH1SigmaSector i 0 = 0 := by
  apply physicalH1SigmaToH1LI.injective
  simp only [physicalH1SigmaSector_toH1, map_zero, physicalH1Sector_zero]

theorem norm_physicalH1SigmaSector_le (i : Fin 6) (u : PhysicalH1Sigma) :
    ‖physicalH1SigmaSector i u‖ ≤ ‖u‖ := by
  rw [← physicalH1SigmaToH1LI.norm_map (physicalH1SigmaSector i u),
    physicalH1SigmaSector_toH1]
  exact (norm_physicalH1Sector_le i (physicalH1SigmaToH1LI u)).trans_eq
    (physicalH1SigmaToH1LI.norm_map u)

/-- The constructed bounded projection on the actual closed solenoidal H1 graph. -/
def physicalH1SigmaSectorCLM (i : Fin 6) : PhysicalH1Sigma →L[ℝ] PhysicalH1Sigma :=
  ({ toFun := physicalH1SigmaSector i
     map_add' := physicalH1SigmaSector_add i
     map_smul' := physicalH1SigmaSector_smul i } :
      PhysicalH1Sigma →ₗ[ℝ] PhysicalH1Sigma).mkContinuous 1
    (fun u => by
      change ‖physicalH1SigmaSector i u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using norm_physicalH1SigmaSector_le i u)

@[simp] theorem physicalH1SigmaSectorCLM_apply (i : Fin 6) (u : PhysicalH1Sigma) :
    physicalH1SigmaSectorCLM i u = physicalH1SigmaSector i u := rfl

theorem physicalH1SigmaSector_idempotent (i : Fin 6) (u : PhysicalH1Sigma) :
    physicalH1SigmaSector i (physicalH1SigmaSector i u) = physicalH1SigmaSector i u := by
  apply physicalH1SigmaToH1LI.injective
  simp only [physicalH1SigmaSector_toH1, physicalH1Sector_idempotent]

theorem physicalH1SigmaSector_comp_eq_zero {i k : Fin 6} (hik : i ≠ k)
    (u : PhysicalH1Sigma) :
    physicalH1SigmaSector i (physicalH1SigmaSector k u) = 0 := by
  apply physicalH1SigmaToH1LI.injective
  simp only [physicalH1SigmaSector_toH1, physicalH1Sector_comp_eq_zero hik, map_zero]

theorem sum_physicalH1SigmaSector (u : PhysicalH1Sigma) :
    (∑ i : Fin 6, physicalH1SigmaSector i u) = u := by
  apply physicalH1SigmaToH1LI.injective
  simp only [map_sum, physicalH1SigmaSector_toH1, sum_physicalH1Sector]

theorem inner_physicalH1SigmaSector_left (i : Fin 6) (u v : PhysicalH1Sigma) :
    inner ℝ (physicalH1SigmaSector i u) v =
      inner ℝ u (physicalH1SigmaSector i v) := by
  rw [← physicalH1SigmaToH1LI.inner_map_map (physicalH1SigmaSector i u) v,
    ← physicalH1SigmaToH1LI.inner_map_map u (physicalH1SigmaSector i v)]
  simp only [physicalH1SigmaSector_toH1]
  exact inner_physicalH1Sector_left i (physicalH1SigmaToH1LI u) (physicalH1SigmaToH1LI v)

theorem inner_physicalH1SigmaSector_eq_zero {i k : Fin 6} (hik : i ≠ k)
    (u v : PhysicalH1Sigma) :
    inner ℝ (physicalH1SigmaSector i u) (physicalH1SigmaSector k v) = 0 := by
  rw [← physicalH1SigmaToH1LI.inner_map_map
    (physicalH1SigmaSector i u) (physicalH1SigmaSector k v)]
  simp only [physicalH1SigmaSector_toH1]
  exact inner_physicalH1Sector_eq_zero hik (physicalH1SigmaToH1LI u) (physicalH1SigmaToH1LI v)

theorem sum_norm_physicalH1SigmaSector_sq (u : PhysicalH1Sigma) :
    (∑ i : Fin 6, ‖physicalH1SigmaSector i u‖ ^ 2) = ‖u‖ ^ 2 := by
  calc
    (∑ i : Fin 6, ‖physicalH1SigmaSector i u‖ ^ 2) =
        ∑ i : Fin 6, ‖physicalH1SigmaToH1LI (physicalH1SigmaSector i u)‖ ^ 2 := by
      simp only [physicalH1SigmaToH1LI.norm_map]
    _ = ∑ i : Fin 6, ‖physicalH1Sector i (physicalH1SigmaToH1LI u)‖ ^ 2 := by
      simp only [physicalH1SigmaSector_toH1]
    _ = ‖physicalH1SigmaToH1LI u‖ ^ 2 :=
      sum_norm_physicalH1Sector_sq (physicalH1SigmaToH1LI u)
    _ = ‖u‖ ^ 2 := by rw [physicalH1SigmaToH1LI.norm_map]

/-- Exact charge additivity on the original solenoidal graph and its actual
weak-gradient components. -/
theorem physicalH1SigmaSector_enstrophy_sum (u : PhysicalH1Sigma) :
    (∑ i : Fin 6, ∑ j : Fin 3, ‖(physicalH1SigmaSector i u).val j.succ‖ ^ 2) =
      ∑ j : Fin 3, ‖u.val j.succ‖ ^ 2 := by
  simpa only [physicalH1Enstrophy_sector, physicalH1SigmaToH1LI_gradient,
    physicalH1Enstrophy, physicalH1Sector_gradient, physicalH1SigmaSector_gradient] using
      sum_physicalH1Enstrophy_sector (physicalH1SigmaToH1LI u)

/-- The native solenoidal projection has the same literal cone charge and
exact physical Fourier normalization as the full H1 projection. -/
theorem physicalH1SigmaSector_charge_eq_sector_integral (i : Fin 6) (u : PhysicalH1Sigma) :
    (∑ j : Fin 3, ‖(physicalH1SigmaSector i u).val j.succ‖ ^ 2) =
      (4 * Real.pi ^ 2) * (∫ ξ : Space in sixSector i, ‖ξ‖ ^ 2 *
        ‖(𝓕 (complexifyL2 (u.val 0)) : ComplexL2) ξ‖ ^ 2) := by
  simpa only [physicalH1SectorCharge_eq, physicalH1SigmaToH1LI_gradient,
    physicalH1SigmaToH1LI_velocity, physicalH1SigmaSector_gradient] using
      physicalH1SectorCharge_eq_sector_integral i (physicalH1SigmaToH1LI u)

end MethbokeAddon.QuasiFeffermanA
