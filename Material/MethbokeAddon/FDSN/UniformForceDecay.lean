import MethbokeAddon.FDSN.Contracts
import SingularClosure.SmoothDatumSobolev
import MethbokeAddon.WeakFouriermanB.PhysicalEnstrophyEvolution

/-!
# Uniform rapid Fourier bounds for the actual smooth periodic force

Finite-order coordinate derivatives remain jointly smooth. Their physical
L1 norms vary continuously on compact time intervals. Thus the existing
pointwise Fourier decay constant is uniformly bounded on `[0,T]`.
No terminal bound on the seed velocity is used.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

open MethbokeAddon.WeakFouriermanB

noncomputable section

theorem initial_iteratedCoordinateDerivative_contDiffOn
    (j : Fin 3) (m : ℕ) (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S)) :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec =>
      iteratedCoordinateDerivative j m (u z.1) z.2) (initialFrontSpacetime S) := by
  induction m with
  | zero => exact hu
  | succ m ih =>
      exact initial_coordinateDerivative_contDiffOn
        (fun t => iteratedCoordinateDerivative j m (u t)) S ih j

theorem initial_coordinateDerivativeL1_continuousOn_Icc
    (j : Fin 3) (m : ℕ) (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (i : Fin 3) (τ : ℝ) (hτS : τ < S) :
    ContinuousOn (fun t => coordinateDerivativeL1 j m (u t) i) (Icc (0 : ℝ) τ) := by
  have hD := initial_iteratedCoordinateDerivative_contDiffOn j m u S hu
  have hc : ContinuousOn (fun z : ℝ × Vec =>
      ‖iteratedCoordinateDerivative j m (u z.1) z.2 i‖) (initialFrontSpacetime S) :=
    ((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp_continuousOn hD.continuousOn).norm
  exact initial_real_cube_integral_continuousOn_Icc S
    (fun t x => ‖iteratedCoordinateDerivative j m (u t) x i‖) hc τ hτS

theorem initial_fourierDecayConstant_continuousOn_Icc
    (m : ℕ) (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (τ : ℝ) (hτS : τ < S) :
    ContinuousOn (fun t => fourierDecayConstant m (u t)) (Icc (0 : ℝ) τ) := by
  unfold fourierDecayConstant
  apply continuousOn_finset_sum
  intro i _
  have hbase := initial_coordinateDerivativeL1_continuousOn_Icc 0 0 u S hu i τ hτS
  apply hbase.add
  apply continuousOn_finset_sum
  intro j _
  exact initial_coordinateDerivativeL1_continuousOn_Icc j m u S hu i τ hτS

theorem initial_smoothDatumDecayConstant_continuousOn_Icc
    (s : ℕ) (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (initialFrontSpacetime S))
    (τ : ℝ) (hτS : τ < S) :
    ContinuousOn (fun t => smoothDatumDecayConstant s (u t)) (Icc (0 : ℝ) τ) :=
  continuousOn_const.mul
    (initial_fourierDecayConstant_continuousOn_Icc (2 * (s + 2)) u S hu τ hτS)

/-- Uniform weighted coefficient decay is derived from the actual globally
smooth periodic force and compactness of the physical time interval. -/
theorem admissibleForce_uniform_fourier_weight_bound {F : Velocity}
    (hF : MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce F)
    (T : ℝ) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Frequency, ∀ i : Fin 3,
      torusSobolevWeight k ^ (s + 2) * ‖datumFourierCoeff (F t) k i‖ ≤ C := by
  have hc : ContinuousOn (fun t => smoothDatumDecayConstant s (F t)) (Icc (0 : ℝ) T) :=
    initial_smoothDatumDecayConstant_continuousOn_Icc s F (T + 1)
      hF.smooth.contDiffOn T (by linarith)
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max B 0, le_max_right B 0, ?_⟩
  intro t ht k i
  have hs : ContDiff ℝ ∞ (F t) :=
    hF.smooth.comp (contDiff_const.prodMk contDiff_id)
  calc
    _ ≤ smoothDatumDecayConstant s (F t) :=
      smooth_datum_sobolev_decay s (F t) hs (hF.periodic t) k i
    _ ≤ ‖smoothDatumDecayConstant s (F t)‖ := by
      simpa only [Real.norm_eq_abs] using le_abs_self (smoothDatumDecayConstant s (F t))
    _ ≤ B := hB t ht
    _ ≤ max B 0 := le_max_left B 0

/-- A single summable envelope for all physical forcing coefficients before T. -/
theorem admissibleForce_uniform_fourier_envelope {F : Velocity}
    (hF : MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce F) (T : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T, ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff (F t) k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4 := by
  obtain ⟨C, hC0, hC⟩ := admissibleForce_uniform_fourier_weight_bound hF T 2
  refine ⟨C, hC0, ?_⟩
  intro t ht k i
  have hb := hC t ht k i
  have hw : 0 < torusSobolevWeight k ^ 4 := pow_pos (torusSobolevWeight_pos k) 4
  have he : ‖datumFourierCoeff (F t) k i‖ ≤ C / torusSobolevWeight k ^ 4 := by
    apply (le_div_iff₀ hw).mpr
    simpa only [Nat.reduceAdd, mul_comm] using hb
  simpa only [div_eq_mul_inv, inv_pow] using he

end

end MethbokeAddon.FDSN
