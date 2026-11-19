import MethbokeAddon.WeakFouriermanB.PhysicalEnstrophyEvolution
import MethbokeAddon.EhrenfestObstruction.SmoothSobolevNorm
import MethbokeAddon.EhrenfestObstruction.ProjectedC1

/-!
Actual smooth-reference estimates on each closed interval strictly inside an
initial classical front. The Fourier-decay constants are the existing physical
integrals of spatial derivatives, and their bounds are obtained by compactness.
Prepared source only: matching external cached compilation and audits remain.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

/-- Repeated ordinary spatial differentiation preserves joint smoothness,
including at the initial time boundary. -/
theorem initial_iteratedCoordinateDerivative_contDiffOn
    (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (initialFrontSpacetime S))
    (j : Fin 3) (m : ℕ) :
    ContDiffOn ℝ ∞
      (fun z : ℝ × Vec => iteratedCoordinateDerivative j m (u z.1) z.2)
      (initialFrontSpacetime S) := by
  induction m with
  | zero => exact hu
  | succ m ih =>
      exact initial_coordinateDerivative_contDiffOn
        (fun t => iteratedCoordinateDerivative j m (u t)) S ih j

/-- The physical component L1 norm is continuous on every shorter closed slab. -/
theorem initial_componentL1_continuousOn_Icc
    (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (initialFrontSpacetime S))
    (i : Fin 3) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => ∫ x in unitCube, ‖u t x i‖) (Icc (0 : ℝ) T) := by
  exact initial_real_cube_integral_continuousOn_Icc S
    (fun t x => ‖u t x i‖)
    (((EuclideanSpace.proj i : Vec →L[ℝ] ℝ).continuous.comp_continuousOn
      hu.continuousOn).norm) T hTS

/-- Every actual coordinate-derivative L1 norm is continuous on a shorter slab. -/
theorem initial_coordinateDerivativeL1_continuousOn_Icc
    (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (initialFrontSpacetime S))
    (j : Fin 3) (m : ℕ) (i : Fin 3) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => coordinateDerivativeL1 j m (u t) i)
      (Icc (0 : ℝ) T) := by
  exact initial_componentL1_continuousOn_Icc
    (fun t => iteratedCoordinateDerivative j m (u t)) S
    (initial_iteratedCoordinateDerivative_contDiffOn u S hu j m) i T hTS

/-- The repository's literal Fourier-decay constant varies continuously in time. -/
theorem initial_fourierDecayConstant_continuousOn_Icc
    (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (initialFrontSpacetime S))
    (m : ℕ) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => fourierDecayConstant m (u t)) (Icc (0 : ℝ) T) := by
  unfold fourierDecayConstant
  apply continuousOn_finset_sum
  intro i _
  apply (initial_componentL1_continuousOn_Icc u S hu i T hTS).add
  apply continuousOn_finset_sum
  intro j _
  exact initial_coordinateDerivativeL1_continuousOn_Icc u S hu j m i T hTS

/-- The actual weighted Fourier-decay constant is continuous on every shorter slab. -/
theorem initial_smoothDatumDecayConstant_continuousOn_Icc
    (u : Velocity) (S : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (initialFrontSpacetime S))
    (s : ℕ) (T : ℝ) (hTS : T < S) :
    ContinuousOn (fun t => smoothDatumDecayConstant s (u t)) (Icc (0 : ℝ) T) := by
  unfold smoothDatumDecayConstant
  exact continuousOn_const.mul
    (initial_fourierDecayConstant_continuousOn_Icc u S hu (2 * (s + 2)) T hTS)

/-- Compactness supplies a uniform Fourier-decay bound from the actual front;
the bound is a conclusion and is not an independent certificate field. -/
theorem initial_front_uniform_decay_constant
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (s : ℕ) (T : ℝ) (hTS : T < S) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ t ∈ Icc (0 : ℝ) T,
      smoothDatumDecayConstant s (u t) ≤ C := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
      (initial_smoothDatumDecayConstant_continuousOn_Icc u S H.velocity_smooth s T hTS)
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro t ht
  have hCt : |smoothDatumDecayConstant s (u t)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC t ht
  exact (le_abs_self _).trans (hCt.trans (le_max_right _ _))

/-- The actual Fourier Sobolev state of the reference field at an admitted time. -/
def initialFrontSobolev (s : ℕ)
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) : TorusSobolev s :=
  smoothDatumSobolev s (u t)
    (initial_front_smooth_slices ν S a u p H t ht).smooth
    (initial_front_smooth_slices ν S a u p H t ht).periodic

@[simp]
theorem initialFrontSobolev_coeff (s : ℕ)
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) :
    (initialFrontSobolev s ν S a u p H t ht).val = datumFourierCoeff (u t) := rfl

/-- Actual physical mean zero supplies the zero mode needed by Galerkin cutoffs. -/
theorem initialFrontSobolev_meanZero (s : ℕ)
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) :
    SpectralMeanZero (initialFrontSobolev s ν S a u p H t ht).val :=
  smoothSigmaZero_fourier_meanZero (initial_front_smooth_slices ν S a u p H t ht)

/-- Every actual smooth reference front has a uniform H^s bound on each
strictly shorter closed interval. No Fourier-norm continuity is postulated. -/
theorem initial_front_uniform_sobolev_norm
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (s : ℕ) (T : ℝ) (hTS : T < S) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ t (ht : t ∈ Icc (0 : ℝ) T),
      ‖initialFrontSobolev s ν S a u p H t ⟨ht.1, ht.2.trans_lt hTS⟩‖ ≤ K := by
  obtain ⟨C, hC, hbound⟩ := initial_front_uniform_decay_constant ν S a u p H s T hTS
  refine ⟨max 1 (Real.sqrt (3 * latticeSobolevConstant) * C), le_max_left _ _, ?_⟩
  intro t ht
  have hsmooth := initial_front_smooth_slices ν S a u p H t
    ⟨ht.1, ht.2.trans_lt hTS⟩
  change ‖smoothDatumSobolev s (u t) hsmooth.smooth hsmooth.periodic‖ ≤ _
  exact (smoothDatumSobolev_norm_le s (u t) hsmooth.smooth hsmooth.periodic).trans
    ((mul_le_mul_of_nonneg_left (hbound t ht) (Real.sqrt_nonneg _)).trans
      (le_max_right _ _))

/-- The actual projected reference enstrophy is bounded independently of cutoff
by physical Bessel and compactness of the smooth front's physical dissipation. -/
theorem initial_front_uniform_projected_dissipation
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (T : ℝ) (hTS : T < S) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ N t (ht : t ∈ Icc (0 : ℝ) T),
      coefficientDissipation N (datumFourierCoeff (u t)) ≤ K := by
  obtain ⟨C, hC⟩ :=
    (isCompact_Icc : IsCompact (Icc (0 : ℝ) T)).exists_bound_of_continuousOn
      (initial_physicalDissipation_continuousOn_Icc u S H.velocity_smooth T hTS)
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro N t ht
  have hsmooth := initial_front_smooth_slices ν S a u p H t
    ⟨ht.1, ht.2.trans_lt hTS⟩
  have hb : coefficientDissipation N (datumFourierCoeff (u t)) ≤
      physicalDissipation (u t) :=
    coefficientDissipation_initial_cutoff_le N (u t) hsmooth.smooth hsmooth.periodic
  have hCt : |physicalDissipation (u t)| ≤ C := by
    simpa only [Real.norm_eq_abs] using hC t ht
  exact hb.trans ((le_abs_self _).trans (hCt.trans (le_max_right _ _)))

/-- The actual projected reference velocity and every coordinate derivative
are bounded uniformly in time, space and cutoff on each shorter closed slab. -/
theorem initial_front_uniform_projected_C1_components
    (ν S : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a u p)
    (T : ℝ) (hTS : T < S) :
    ∃ B : ℝ, 1 ≤ B ∧ ∀ N t (ht : t ∈ Icc (0 : ℝ) T) (x : Vec),
      (∀ i : Fin 3, |finiteSynthesis N (datumFourierCoeff (u t)) x i| ≤ B) ∧
      (∀ j i : Fin 3,
        |coordinateDerivative (finiteSynthesis N (datumFourierCoeff (u t))) j x i| ≤ B) := by
  obtain ⟨K, hK, hbound⟩ := initial_front_uniform_sobolev_norm ν S a u p H 3 T hTS
  refine ⟨max 1 (Real.sqrt latticeSobolevConstant * K), le_max_left _ _, ?_⟩
  intro N t ht x
  have h := finiteSynthesis_C1_components_le_H3_norm N
    (initialFrontSobolev 3 ν S a u p H t ⟨ht.1, ht.2.trans_lt hTS⟩) x
  have hb : Real.sqrt latticeSobolevConstant *
      ‖initialFrontSobolev 3 ν S a u p H t ⟨ht.1, ht.2.trans_lt hTS⟩‖ ≤
      max 1 (Real.sqrt latticeSobolevConstant * K) :=
    (mul_le_mul_of_nonneg_left (hbound t ht) (Real.sqrt_nonneg _)).trans
      (le_max_right _ _)
  exact ⟨fun i => (h.1 i).trans hb, fun j i => (h.2 j i).trans hb⟩

end
end MethbokeAddon.EhrenfestObstruction
