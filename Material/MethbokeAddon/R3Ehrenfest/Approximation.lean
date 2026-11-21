import MethbokeAddon.R3Ehrenfest.SharpCutoff
import QFALC001Reduction.NativeFromAENorms
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.MetricSpace.Equicontinuity
import Mathlib.Topology.UniformSpace.Ascoli

/-!
# Strong and compact-uniform approximation by the actual sharp cutoffs

For every actual L2 field the frequency error vanishes pointwise eventually,
and its squared norm is dominated by the original integrable Fourier energy.
Dominated convergence and the constructed inverse Fourier map therefore give
strong L2 approximation. Applying this to the existing physical weak-gradient
components gives strong approximation in the native physical H1 norm.

The uniform contraction bound upgrades this convergence to uniform convergence
on each compact subset of physical H1, including every continuous trajectory
on a compact time interval. Compactness is used only for that supplied compact
set or trajectory image; no norm ball or bandlimited carrier is declared compact.

These are approximation results. No PDE evolution, nonlinear estimate or
Navier--Stokes root conclusion is asserted. Prepared source requires matching
authorized external cached compilation and named axiom evidence.
-/

set_option autoImplicit false
set_option Elab.async true
set_option maxHeartbeats 800000

noncomputable section

open Set Filter MeasureTheory FourierTransform
open scoped BigOperators FourierTransform Topology UniformConvergence

namespace MethbokeAddon.R3Ehrenfest.Approximation

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.RealFourier
open MethbokeAddon.QuasiFeffermanA.RealEvenMultipliers
open QFA.Endpoints.Agmon (ComplexL2 ComplexVector)
open QFA.Endpoints.Representation
open QFA.LC001SpectralReduction
open SharpCutoff

/-- Each fixed frequency eventually lies in every subsequent cutoff ball. -/
theorem cutoffValue_eventually_one (ξ : Space) :
    ∀ᶠ n : ℕ in atTop, cutoffValue n ξ = 1 := by
  obtain ⟨N, hN⟩ := exists_nat_gt ‖ξ‖
  filter_upwards [eventually_ge_atTop N] with n hn
  have hcast : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hinside : ‖ξ‖ ≤ cutoffRadius n := by
    unfold cutoffRadius
    linarith
  simp only [cutoffValue, if_pos hinside]

private theorem tendsto_of_norm_sq_sub_zero {E : Type*} [NormedAddCommGroup E]
    {F : ℕ → E} {f : E}
    (h : Tendsto (fun n => ‖F n - f‖ ^ 2) atTop (𝓝 (0 : ℝ))) :
    Tendsto F atTop (𝓝 f) := by
  rw [tendsto_iff_dist_tendsto_zero]
  simpa [Real.sqrt_sq_eq_abs, dist_eq_norm] using h.sqrt

/-- Strong approximation of every actual complex frequency-space L2 field. -/
theorem tendsto_frequencyMultiplier_cutoff (f : ComplexL2) :
    Tendsto (fun n : ℕ => frequencyMultiplier (cutoffSymbol n) f) atTop (𝓝 f) := by
  have hformula : ∀ᵐ ξ : Space ∂volume, ∀ n : ℕ,
      (frequencyMultiplier (cutoffSymbol n) f - f) ξ =
        (cutoffValue n ξ : ℂ) • f ξ - f ξ := by
    apply ae_all_iff.mpr
    intro n
    filter_upwards [frequencyMultiplier_ae (cutoffSymbol n) f,
      Lp.coeFn_sub (frequencyMultiplier (cutoffSymbol n) f) f] with ξ hm hs
    exact hs.trans (congrArg (fun z : ComplexVector => z - f ξ) hm)
  have hmeas (n : ℕ) : AEStronglyMeasurable
      (fun ξ : Space => ‖(frequencyMultiplier (cutoffSymbol n) f - f) ξ‖ ^ 2) volume :=
    ((Lp.aestronglyMeasurable (frequencyMultiplier (cutoffSymbol n) f - f)).norm.aemeasurable.pow_const
      2).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ ξ : Space ∂volume,
      ‖‖(frequencyMultiplier (cutoffSymbol n) f - f) ξ‖ ^ 2‖ ≤ ‖f ξ‖ ^ 2 := by
    filter_upwards [hformula] with ξ hξ
    rw [hξ n]
    by_cases h : ‖ξ‖ ≤ cutoffRadius n <;> simp [cutoffValue, h]
  have hlim : ∀ᵐ ξ : Space ∂volume,
      Tendsto (fun n : ℕ => ‖(frequencyMultiplier (cutoffSymbol n) f - f) ξ‖ ^ 2)
        atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [hformula] with ξ hξ
    apply (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
    filter_upwards [cutoffValue_eventually_one ξ] with n hn
    have hz : (frequencyMultiplier (cutoffSymbol n) f - f) ξ = 0 := by
      rw [hξ n, hn]
      simp
    change (0 : ℝ) = ‖(frequencyMultiplier (cutoffSymbol n) f - f) ξ‖ ^ (2 : ℕ)
    calc
      (0 : ℝ) = ‖(0 : ComplexVector)‖ ^ (2 : ℕ) := by norm_num
      _ = ‖(frequencyMultiplier (cutoffSymbol n) f - f) ξ‖ ^ (2 : ℕ) :=
        congrArg (fun z : ComplexVector => (‖z‖ : ℝ) ^ (2 : ℕ)) hz.symm
  have hDCT := tendsto_integral_of_dominated_convergence
    (F := fun n ξ => ‖(frequencyMultiplier (cutoffSymbol n) f - f) ξ‖ ^ 2)
    (f := fun _ : Space => (0 : ℝ)) (fun ξ : Space => ‖f ξ‖ ^ 2)
    hmeas (integrable_norm_sq f) hbound hlim
  apply tendsto_of_norm_sq_sub_zero
  simpa only [integral_norm_sq_eq_norm_sq, integral_zero] using hDCT

/-- The concrete real whole-space L2 cutoffs converge strongly to every input. -/
theorem tendsto_sharpCutoff (u : SpatialL2) :
    Tendsto (fun n : ℕ => sharpCutoff n u) atTop (𝓝 u) := by
  have hfreq := tendsto_frequencyMultiplier_cutoff (𝓕 (complexifyL2 u) : ComplexL2)
  have hreal : Tendsto
      (fun n : ℕ => realPartL2CLM
        (𝓕⁻ (frequencyMultiplier (cutoffSymbol n) (𝓕 (complexifyL2 u)))))
      atTop (𝓝 (realPartL2CLM (𝓕⁻ (𝓕 (complexifyL2 u))))) :=
    ((realPartL2CLM.continuous.comp
      (Lp.fourierTransformₗᵢ Space ComplexVector).symm.continuous).tendsto _).comp hfreq
  simpa only [fourierInv_fourier_eq, realPartL2_complexify,
    sharpCutoff_apply, realFourierMultiplier] using hreal

theorem norm_sharpCutoff_sub_tendsto_zero (u : SpatialL2) :
    Tendsto (fun n : ℕ => ‖sharpCutoff n u - u‖) atTop (𝓝 (0 : ℝ)) := by
  simpa only [sub_self, norm_zero] using
    ((tendsto_sharpCutoff u).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u))).norm

/-- Strong approximation in the original physical H1 graph norm. -/
theorem tendsto_physicalH1SharpCutoff (u : PhysicalH1) :
    Tendsto (fun n : ℕ => physicalH1SharpCutoff n u) atTop (𝓝 u) := by
  have hv := (norm_sharpCutoff_sub_tendsto_zero (physicalH1Velocity u)).pow 2
  have hg (j : Fin 3) := (norm_sharpCutoff_sub_tendsto_zero (physicalH1Gradient j u)).pow 2
  have hs := tendsto_finsetSum Finset.univ (fun j _ => hg j)
  have hsum := hv.add hs
  apply tendsto_of_norm_sq_sub_zero
  simpa only [physicalH1_norm_sq, map_sub, physicalH1SharpCutoff_velocity,
    physicalH1SharpCutoff_gradient, zero_pow (by decide : (2 : ℕ) ≠ 0),
    Finset.sum_const_zero, zero_add] using hsum

theorem tendsto_physicalH1SharpCutoffCLM (u : PhysicalH1) :
    Tendsto (fun n : ℕ => physicalH1SharpCutoffCLM n u) atTop (𝓝 u) :=
  tendsto_physicalH1SharpCutoff u

theorem norm_physicalH1SharpCutoff_sub_tendsto_zero (u : PhysicalH1) :
    Tendsto (fun n : ℕ => ‖physicalH1SharpCutoff n u - u‖) atTop (𝓝 (0 : ℝ)) := by
  simpa only [sub_self, norm_zero] using
    ((tendsto_physicalH1SharpCutoff u).sub
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => u) atTop (𝓝 u))).norm

/-- A common contraction modulus, uniform in the cutoff radius. -/
theorem dist_physicalH1SharpCutoff_le (n : ℕ) (u v : PhysicalH1) :
    dist (physicalH1SharpCutoff n u) (physicalH1SharpCutoff n v) ≤ dist u v := by
  change dist (physicalH1SharpCutoffCLM n u) (physicalH1SharpCutoffCLM n v) ≤ dist u v
  rw [dist_eq_norm, ← map_sub, dist_eq_norm]
  exact norm_physicalH1SharpCutoff_le n (u - v)

/-- Uniform physical H1 approximation on each genuinely compact subset. -/
theorem tendstoUniformlyOn_physicalH1SharpCutoff (K : Set PhysicalH1) (hK : IsCompact K) :
    TendstoUniformlyOn (fun n : ℕ => physicalH1SharpCutoff n) (fun u => u) atTop K := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hequi : Equicontinuous (fun (n : ℕ) (u : K) => physicalH1SharpCutoff n u) := by
    apply Metric.equicontinuous_of_continuity_modulus (fun r : ℝ => r) tendsto_id
    intro u v n
    exact dist_physicalH1SharpCutoff_le n u v
  have hpoint : Tendsto (fun (n : ℕ) (u : K) => physicalH1SharpCutoff n u) atTop
      (𝓝 (fun u : K => (u : PhysicalH1))) := by
    rw [tendsto_pi_nhds]
    intro u
    exact tendsto_physicalH1SharpCutoff u
  have huniform := (hequi.tendsto_uniformFun_iff_pi atTop
    (fun u : K => (u : PhysicalH1))).mpr hpoint
  apply tendstoUniformlyOn_iff_tendstoUniformly_comp_coe.mpr
  exact UniformFun.tendsto_iff_tendstoUniformly.mp huniform

/-- Every continuous physical H1 trajectory has uniformly vanishing cutoff tails
on each compact nonnegative time interval. -/
theorem tendstoUniformlyOn_physicalH1SharpCutoff_trajectory
    (U : ℝ → PhysicalH1) (T : ℝ) (hU : ContinuousOn U (Icc 0 T)) :
    TendstoUniformlyOn (fun n : ℕ => fun t : ℝ => physicalH1SharpCutoff n (U t))
      U atTop (Icc 0 T) := by
  have hcompact : IsCompact (U '' Icc 0 T) := isCompact_Icc.image_of_continuousOn hU
  have h := (tendstoUniformlyOn_physicalH1SharpCutoff (U '' Icc 0 T) hcompact).comp U
  exact h.mono (fun t ht => ⟨t, ht, rfl⟩)

end MethbokeAddon.R3Ehrenfest.Approximation
