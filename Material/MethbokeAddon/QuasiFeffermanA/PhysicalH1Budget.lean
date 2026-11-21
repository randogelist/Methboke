import MethbokeAddon.QuasiFeffermanA.PhysicalH1
import MethbokeAddon.QuasiFeffermanA.ACBudget

/-!
# Actual physical H1 energy, enstrophy and finite-slab budgets

The observables are the squared L2 norm of the actual velocity and the sum of
the squared L2 norms of its actual weak derivatives. Their sum is the exact
inhomogeneous H1 norm squared on full Euclidean space. An independent energy
bound and an enstrophy bound therefore control this norm without Poincare.

A supplied path continuous on a full closed finite time slab has a finite
full stopped square-enstrophy budget, by genuine integrability of a continuous
nonnegative integrand. A separate conditional estimate composes the scalar
AC/cubic theorem with an explicit energy bound for the supplied path.

No NSE existence, energy inequality, physical enstrophy evolution or terminal
path extension is constructed here. In particular, continuity on each shorter
closed interval is not substituted for continuity on the full closed slab.
Prepared source requires matching authorized external verification.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open Set MeasureTheory Filter
open scoped BigOperators Interval ENNReal Topology

namespace MethbokeAddon.QuasiFeffermanA

/-- The squared actual velocity L2 norm, with no one-half normalization. -/
def physicalH1Energy (u : PhysicalH1) : ℝ :=
  ‖physicalH1Velocity u‖ ^ 2

/-- The squared full-gradient L2 norm of the actual physical weak derivatives. -/
def physicalH1Enstrophy (u : PhysicalH1) : ℝ :=
  ∑ j : Fin 3, ‖physicalH1Gradient j u‖ ^ 2

theorem physicalH1Energy_nonneg (u : PhysicalH1) : 0 ≤ physicalH1Energy u :=
  sq_nonneg _

theorem physicalH1Enstrophy_nonneg (u : PhysicalH1) : 0 ≤ physicalH1Enstrophy u :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem physicalH1Energy_continuous : Continuous physicalH1Energy :=
  physicalH1Velocity.continuous.norm.pow 2

theorem physicalH1Enstrophy_continuous : Continuous physicalH1Enstrophy := by
  unfold physicalH1Enstrophy
  exact continuous_finsetSum Finset.univ
    (fun j _ => (physicalH1Gradient j).continuous.norm.pow 2)

/-- Exact inhomogeneous norm accounting on the constructed full-space graph. -/
theorem physicalH1_norm_sq_eq_energy_add_enstrophy (u : PhysicalH1) :
    ‖u‖ ^ 2 = physicalH1Energy u + physicalH1Enstrophy u :=
  physicalH1_norm_sq u

theorem physicalH1Energy_le_norm_sq (u : PhysicalH1) :
    physicalH1Energy u ≤ ‖u‖ ^ 2 := by
  rw [physicalH1_norm_sq_eq_energy_add_enstrophy]
  exact le_add_of_nonneg_right (physicalH1Enstrophy_nonneg u)

theorem physicalH1Enstrophy_le_norm_sq (u : PhysicalH1) :
    physicalH1Enstrophy u ≤ ‖u‖ ^ 2 := by
  rw [physicalH1_norm_sq_eq_energy_add_enstrophy]
  exact le_add_of_nonneg_left (physicalH1Energy_nonneg u)

/-- Separate velocity-energy and enstrophy bounds give the full H1 bound. -/
theorem physicalH1_norm_sq_le_of_energy_enstrophy (u : PhysicalH1) {E0 B : ℝ}
    (hE : physicalH1Energy u ≤ E0) (hY : physicalH1Enstrophy u ≤ B) :
    ‖u‖ ^ 2 ≤ E0 + B := by
  rw [physicalH1_norm_sq_eq_energy_add_enstrophy]
  exact add_le_add hE hY

/-- Pointwise bounds with common constants give a uniform bound on any time set. -/
theorem physicalH1_path_norm_sq_le (U : ℝ → PhysicalH1) (s : Set ℝ) {E0 B : ℝ}
    (hE : ∀ t ∈ s, physicalH1Energy (U t) ≤ E0)
    (hY : ∀ t ∈ s, physicalH1Enstrophy (U t) ≤ B) :
    ∀ t ∈ s, ‖U t‖ ^ 2 ≤ E0 + B := by
  intro t ht
  exact physicalH1_norm_sq_le_of_energy_enstrophy (U t) (hE t ht) (hY t ht)

/-- Closed-slab H1 continuity gives genuine integrability of squared enstrophy. -/
theorem physicalH1_enstrophy_sq_integrableOn_Icc
    (U : ℝ → PhysicalH1) {b : ℝ} (hU : ContinuousOn U (Icc (0 : ℝ) b)) :
    IntegrableOn (fun t => (physicalH1Enstrophy (U t)) ^ 2)
      (Icc (0 : ℝ) b) volume :=
  ((physicalH1Enstrophy_continuous.comp_continuousOn hU).pow 2).integrableOn_Icc

/-- The full stopped extended budget equals the ofReal of its actual integral.
Integrability is proved from continuity on the full closed slab first. -/
theorem physicalH1_stoppedSquareBudget_eq_integral
    (U : ℝ → PhysicalH1) {b : ℝ} (hU : ContinuousOn U (Icc (0 : ℝ) b)) :
    stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b =
      ENNReal.ofReal (∫ t in Ioo (0 : ℝ) b, (physicalH1Enstrophy (U t)) ^ 2) := by
  unfold stoppedSquareBudget
  exact (ofReal_integral_eq_lintegral_ofReal
    ((physicalH1_enstrophy_sq_integrableOn_Icc U hU).mono_set Ioo_subset_Icc_self)
    (Eventually.of_forall (fun t => sq_nonneg (physicalH1Enstrophy (U t))))).symm

/-- A supplied closed-slab H1 path has a finite full stopped enstrophy budget.
This includes empty windows and requires no time derivative or PDE premise. -/
theorem physicalH1_stoppedSquareBudget_finite
    (U : ℝ → PhysicalH1) {b : ℝ} (hU : ContinuousOn U (Icc (0 : ℝ) b)) :
    stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b ≠ ∞ := by
  rw [physicalH1_stoppedSquareBudget_eq_integral U hU]
  exact ENNReal.ofReal_ne_top

/-- The scalar AC/cubic budget estimate controls the actual full H1 norm when
the supplied path also satisfies an explicit velocity-energy bound. -/
theorem physicalH1_ac_cubic_uniform_norm_sq
    (U : ℝ → PhysicalH1) {κ b E0 : ℝ} (hκ : 0 ≤ κ)
    (hE : ∀ t ∈ Ico (0 : ℝ) b, physicalH1Energy (U t) ≤ E0)
    (hAC : ∀ R ∈ Ico (0 : ℝ) b,
      AbsolutelyContinuousOnInterval (fun t => physicalH1Enstrophy (U t)) 0 R)
    (hcubic : ∀ᵐ r ∂volume.restrict (Ioo (0 : ℝ) b),
      deriv (fun t => physicalH1Enstrophy (U t)) r ≤
        κ * (physicalH1Enstrophy (U r)) ^ 3)
    (hbudget : stoppedSquareBudget (fun t => physicalH1Enstrophy (U t)) b ≠ ∞) :
    ∀ t ∈ Ico (0 : ℝ) b,
      ‖U t‖ ^ 2 ≤ E0 + physicalH1Enstrophy (U 0) * Real.exp
        (κ * (stoppedSquareBudget (fun r => physicalH1Enstrophy (U r)) b).toReal) := by
  have hY := ac_cubic_uniform_of_finite_stopped_budget
    hκ (physicalH1Enstrophy_nonneg (U 0)) hAC hcubic hbudget
  intro t ht
  exact physicalH1_norm_sq_le_of_energy_enstrophy (U t) (hE t ht) (hY t ht)

end MethbokeAddon.QuasiFeffermanA
