import MethbokeAddon.QuasiFeffermanA.HeatSemigroup
import MethbokeAddon.QuasiFeffermanA.PhysicalH2

/-!
# The actual strongly continuous physical H2 heat semigroup

Heat acts on the actual velocity, the three actual weak gradients and the
nine actual weak Hessian fields. The accepted weak-gradient heat theorem
proves that these thirteen fields remain in the native closed H2 graph.
The graph Laplacian and H2-to-H1 inclusion commute with this construction.
Full graph contraction and strong continuity follow componentwise from
the accepted physical L2 semigroup, including both zero time and zero
viscosity. The initial trace is the original actual H2 datum.

No higher derivative, temporal regularity, semigroup or continuity witness
is supplied. This constructs the H2 heat action needed for regular forcing;
it makes no arbitrary-H1 H2 initial-trace or forced maximal-regularity claim.

Prepared source requires matching external compilation and independent
named type/axiom evidence. No local Lean, Lake or kernel execution is used.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Filter
open scoped BigOperators NNReal Topology

namespace MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup

open HeatSemigroup

/-- Heat each actual graph coordinate; native weak differentiation commutes
with the same physical L2 heat operator at both derivative levels. -/
def heatH2 (ν t : ℝ≥0) (u : PhysicalH2) : PhysicalH2 :=
  physicalH2OfWeakDerivatives (heatL2 ν t (physicalH2Velocity u))
    (fun j => heatL2 ν t (physicalH2Gradient j u))
    (fun j k => heatL2 ν t (physicalH2Hessian j k u))
    (spatialWeakGradient_heatL2 ν t (physicalH2_weakGradient u))
    (fun j => spatialWeakGradient_heatL2 ν t (physicalH2_weakHessian u j))

@[simp] theorem heatH2_velocity (ν t : ℝ≥0) (u : PhysicalH2) :
    physicalH2Velocity (heatH2 ν t u) = heatL2 ν t (physicalH2Velocity u) := rfl

@[simp] theorem heatH2_gradient (ν t : ℝ≥0) (u : PhysicalH2) (j : Fin 3) :
    physicalH2Gradient j (heatH2 ν t u) = heatL2 ν t (physicalH2Gradient j u) := rfl

@[simp] theorem heatH2_hessian (ν t : ℝ≥0) (u : PhysicalH2) (j k : Fin 3) :
    physicalH2Hessian j k (heatH2 ν t u) = heatL2 ν t (physicalH2Hessian j k u) := rfl

/-- The literal physical Laplacian commutes with the constructed H2 heat action. -/
theorem heatH2_laplacian (ν t : ℝ≥0) (u : PhysicalH2) :
    physicalH2Laplacian (heatH2 ν t u) = heatL2 ν t (physicalH2Laplacian u) := by
  rw [physicalH2Laplacian_apply, physicalH2Laplacian_apply]
  simp only [heatH2_hessian]
  change (∑ j : Fin 3, heatL2CLM ν t (physicalH2Hessian j j u)) =
    heatL2CLM ν t (∑ j : Fin 3, physicalH2Hessian j j u)
  exact ((heatL2CLM ν t).map_sum (fun j : Fin 3 => physicalH2Hessian j j u)
    Finset.univ).symm

/-- The actual H2 action restricts to the already constructed physical H1 heat path. -/
theorem heatH2_toH1 (ν t : ℝ≥0) (u : PhysicalH2) :
    physicalH2ToH1 (heatH2 ν t u) = heatH1 ν t (physicalH2ToH1 u) := by
  apply physicalH1Velocity_injective
  simp only [physicalH2ToH1_velocity, heatH2_velocity, heatH1_velocity]

theorem heatH2_add (ν t : ℝ≥0) (u v : PhysicalH2) :
    heatH2 ν t (u + v) = heatH2 ν t u + heatH2 ν t v := by
  apply physicalH2Velocity_injective
  simp only [heatH2_velocity, map_add, heatL2_add]

theorem heatH2_smul (ν t : ℝ≥0) (r : ℝ) (u : PhysicalH2) :
    heatH2 ν t (r • u) = r • heatH2 ν t u := by
  apply physicalH2Velocity_injective
  simp only [heatH2_velocity, map_smul, heatL2_smul]

private theorem heatH2_norm_sq_le (ν t : ℝ≥0) (u : PhysicalH2) :
    ‖heatH2 ν t u‖ ^ 2 ≤ ‖u‖ ^ 2 := by
  rw [physicalH2_norm_sq, physicalH2_norm_sq]
  simp only [heatH2_velocity, heatH2_gradient, heatH2_hessian]
  apply add_le_add
  · apply add_le_add
    · exact pow_le_pow_left₀ (norm_nonneg _) (norm_heatL2_le ν t _) 2
    · exact Finset.sum_le_sum (fun j _ =>
        pow_le_pow_left₀ (norm_nonneg _) (norm_heatL2_le ν t _) 2)
  · exact Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ =>
      pow_le_pow_left₀ (norm_nonneg _) (norm_heatL2_le ν t _) 2))

/-- Contraction preserves the full inhomogeneous norm of all thirteen graph fields. -/
theorem norm_heatH2_le (ν t : ℝ≥0) (u : PhysicalH2) :
    ‖heatH2 ν t u‖ ≤ ‖u‖ :=
  (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp (heatH2_norm_sq_le ν t u)

/-- The actual bounded real linear heat action on the complete physical H2 graph. -/
def heatH2CLM (ν t : ℝ≥0) : PhysicalH2 →L[ℝ] PhysicalH2 :=
  ({ toFun := heatH2 ν t
     map_add' := heatH2_add ν t
     map_smul' := heatH2_smul ν t } : PhysicalH2 →ₗ[ℝ] PhysicalH2).mkContinuous 1
    (fun u => by
      change ‖heatH2 ν t u‖ ≤ 1 * ‖u‖
      simpa only [one_mul] using norm_heatH2_le ν t u)

@[simp] theorem heatH2CLM_apply (ν t : ℝ≥0) (u : PhysicalH2) :
    heatH2CLM ν t u = heatH2 ν t u := rfl

/-- The original physical H2 datum is the exact initial trace. -/
@[simp] theorem heatH2_zero_time (ν : ℝ≥0) (u : PhysicalH2) :
    heatH2 ν 0 u = u := by
  apply physicalH2Velocity_injective
  simp only [heatH2_velocity, heatL2_zero_time]

@[simp] theorem heatH2_zero_viscosity (t : ℝ≥0) (u : PhysicalH2) :
    heatH2 0 t u = u := by
  apply physicalH2Velocity_injective
  simp only [heatH2_velocity, heatL2_zero_viscosity]

/-- The actual H2 semigroup law, including both zero cases. -/
theorem heatH2_add_time (ν s t : ℝ≥0) (u : PhysicalH2) :
    heatH2 ν (s + t) u = heatH2 ν s (heatH2 ν t u) := by
  apply physicalH2Velocity_injective
  simp only [heatH2_velocity, heatL2_add_time]

private theorem continuous_of_squared_distances
    {E : Type*} [NormedAddCommGroup E] (f : ℝ≥0 → E)
    (h : ∀ s : ℝ≥0, Continuous (fun t : ℝ≥0 => ‖f t - f s‖ ^ 2)) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro s
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hsq : Tendsto (fun t : ℝ≥0 => ‖f t - f s‖ ^ 2) (𝓝 s) (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
      (h s).tendsto s
  have hsqrt := (Real.continuous_sqrt.tendsto (0 : ℝ)).comp hsq
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hsqrt

/-- Strong continuity in the actual H2 graph includes time zero and zero
viscosity. It retains the original H2 velocity, gradient and Hessian trace. -/
theorem heatH2_continuous (ν : ℝ≥0) (u : PhysicalH2) :
    Continuous (fun t : ℝ≥0 => heatH2 ν t u) := by
  apply continuous_of_squared_distances
  intro s
  have hv : Continuous (fun t : ℝ≥0 =>
      ‖heatL2 ν t (physicalH2Velocity u) - heatL2 ν s (physicalH2Velocity u)‖ ^ 2) :=
    ((heatL2_continuous ν (physicalH2Velocity u)).sub continuous_const).norm.pow 2
  have hG : Continuous (fun t : ℝ≥0 => ∑ j : Fin 3,
      ‖heatL2 ν t (physicalH2Gradient j u) - heatL2 ν s (physicalH2Gradient j u)‖ ^ 2) :=
    continuous_finsetSum Finset.univ (fun j _ =>
      ((heatL2_continuous ν (physicalH2Gradient j u)).sub continuous_const).norm.pow 2)
  have hH : Continuous (fun t : ℝ≥0 => ∑ j : Fin 3, ∑ k : Fin 3,
      ‖heatL2 ν t (physicalH2Hessian j k u) -
        heatL2 ν s (physicalH2Hessian j k u)‖ ^ 2) :=
    continuous_finsetSum Finset.univ (fun j _ =>
      continuous_finsetSum Finset.univ (fun k _ =>
        ((heatL2_continuous ν (physicalH2Hessian j k u)).sub continuous_const).norm.pow 2))
  have hsum := (hv.add hG).add hH
  simpa only [physicalH2_norm_sq, map_sub, heatH2_velocity, heatH2_gradient,
    heatH2_hessian] using hsum

end MethbokeAddon.QuasiFeffermanA.HeatH2Semigroup
