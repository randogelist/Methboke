import MethbokeAddon.EhrenfestObstruction.ErrorEquation
import MethbokeAddon.EhrenfestObstruction.ErrorState
import MethbokeAddon.EhrenfestObstruction.PhysicalReferenceTail
import MethbokeAddon.EhrenfestObstruction.ReferenceC1Norm

/-!
The cutoff-uniform cubic inequality for the actual canonical Galerkin error.
All constants are obtained from the actual smooth classical front on a
strictly shorter closed time slab. No error bound, residual estimate, or
evolution certificate is an input to the final theorem.

Prepared source: external cached compiler and axiom audit are still required.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open MethbokeAddon.WeakFouriermanB
open scoped BigOperators ContDiff RealInnerProductSpace

namespace MethbokeAddon.EhrenfestObstruction

noncomputable section

/-- The actual classical front forces a uniform cubic H1 error inequality,
with an actual truncation error decaying as the inverse squared cutoff. -/
theorem initial_front_canonical_error_differential_inequality
    (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S T : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (hTS : T < S) :
    ∃ C A : ℝ, 0 < C ∧ 0 < A ∧ ∀ n t, t ∈ Ioo (0 : ℝ) T →
      ∃ d : ℝ,
        HasDerivAt
          (fun r => coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n r))
          d t ∧
        d ≤ C * (coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t) +
              (coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t)) ^ 3) +
            A / (((n + 1 : ℕ) : ℝ) ^ 2) := by
  obtain ⟨C₀, hC₀, hcross⟩ := FINITE_ERROR_CROSS_ENSTROPHY_INEQUALITY
  obtain ⟨M, hM, hnorm⟩ := initial_front_uniform_C1_norms ν S a.val u p H T hTS
  obtain ⟨K, hK, htail⟩ := initial_front_uniform_physical_H1_tail ν S a.val u p H T hTS
  have hMpos : 0 < M := by linarith
  have hKpos : 0 < K := by linarith
  let C : ℝ := C₀ / ν ^ 3 + 24 * M ^ 2 / ν + 1
  let A : ℝ := 432 * M ^ 2 * K ^ 2 / ν
  have hC : 0 < C := by dsimp [C]; positivity
  have hA : 0 < A := by dsimp [A]; positivity
  have hL : C₀ / ν ^ 3 ≤ C := by
    dsimp [C]
    have hB : 0 ≤ 24 * M ^ 2 / ν := by positivity
    linarith
  have hB : 24 * M ^ 2 / ν ≤ C := by
    dsimp [C]
    have hL₀ : 0 ≤ C₀ / ν ^ 3 := by positivity
    linarith
  refine ⟨C, A, hC, hA, ?_⟩
  intro n t ht
  have htS : t ∈ Ioo (0 : ℝ) S := ⟨ht.1, ht.2.trans hTS⟩
  have htIcc : t ∈ Icc (0 : ℝ) T := ⟨ht.1.le, ht.2.le⟩
  have htIco : t ∈ Ico (0 : ℝ) S := ⟨ht.1.le, htS.2⟩
  let b : FourierCoeff := cutoffCoeff (n + 1) (datumFourierCoeff (u t))
  let v : Field := finiteSynthesis (n + 1) b
  let r : Field := u t - v
  let R : Field := physicalReferenceResidual (u t) v r
  have hUs := initial_front_smooth_slices ν S a.val u p H t htIco
  have hvs : ContDiff ℝ ∞ v := finiteSynthesis_contDiff (n + 1) b
  have hrs : ContDiff ℝ ∞ r := hUs.smooth.sub hvs
  have hRc : Continuous R := physicalReferenceResidual_continuous (u t) v r
    hUs.smooth hvs.continuous hrs
  have hvM : ∀ x ∈ unitCube, ‖v x‖ ≤ M := by
    intro x hx
    simpa only [v, b, finiteSynthesis_cutoffCoeff] using
      (hnorm (n + 1) t htIcc x hx).1
  have hDvM : ∀ x ∈ unitCube, ‖fderiv ℝ v x‖ ≤ M := by
    intro x hx
    simpa only [v, b, finiteSynthesis_cutoffCoeff] using
      (hnorm (n + 1) t htIcc x hx).2.1
  have hDUM : ∀ x ∈ unitCube, ‖fderiv ℝ (u t) x‖ ≤ M :=
    fun x hx => (hnorm (n + 1) t htIcc x hx).2.2
  have hRbound := physicalReferenceResidual_l2_le M hMpos.le (u t) v r
    hUs.smooth hvs.continuous hrs hDUM hvM
  have hrtail : (∫ x in unitCube, ‖r x‖ ^ 2) + physicalDissipation r ≤
      12 * (((n + 1 : ℕ) : ℝ)⁻¹ * K) ^ 2 := by
    simpa only [r, v, b, physicalReferenceTail, finiteSynthesis_cutoffCoeff] using
      htail n t htIcc
  have hRsmall : (∫ x in unitCube, ‖R x‖ ^ 2) ≤
      (6 * M ^ 2) * (12 * (((n + 1 : ℕ) : ℝ)⁻¹ * K) ^ 2) :=
    hRbound.trans (mul_le_mul_of_nonneg_left hrtail (by positivity))
  have heq : ∀ k ∈ cutoffModes (n + 1), ∀ i : Fin 3,
      HasDerivWithinAt (fun q => canonicalErrorCoeff ν hν a u n q k i)
        (galerkinRhs ν (n + 1) (canonicalErrorCoeff ν hν a u n t) k i +
          cutoffCoeff (n + 1) (fun l => coefficientLeray l
            (datumFourierCoeff (physicalErrorForcing v
              (finiteSynthesis (n + 1) (canonicalErrorCoeff ν hν a u n t)) R) l)) k i)
        univ t := by
    intro k hk i
    exact (initial_front_galerkin_error_hasDerivAt ν S a.val u p H (n + 1)
      (canonicalFamily ν hν a n) t htS k hk i).hasDerivWithinAt
  obtain ⟨d, hd, hineq⟩ := hcross ν hν M hMpos.le (n + 1)
    (canonicalErrorCoeff ν hν a u n) v R hvs hRc hvM hDvM univ t
    (canonicalErrorCoeff_support ν hν a u n t ht.1.le)
    (canonicalErrorCoeff_reality ν hν a u n t ht.1.le)
    (canonicalErrorCoeff_solenoidal_front ν hν a S u p H n t htIco) heq
  refine ⟨d, hd.hasDerivAt (by simp), ?_⟩
  have hN : 0 < ((n + 1 : ℕ) : ℝ) := by positivity
  have hforce : (6 / ν) * (∫ x in unitCube, ‖R x‖ ^ 2) ≤
      A / (((n + 1 : ℕ) : ℝ) ^ 2) := by
    calc
      _ ≤ (6 / ν) * ((6 * M ^ 2) *
          (12 * (((n + 1 : ℕ) : ℝ)⁻¹ * K) ^ 2)) :=
        mul_le_mul_of_nonneg_left hRsmall (by positivity)
      _ = _ := by
        dsimp [A]
        field_simp [hν.ne', hN.ne'] <;> ring
  have hD := coefficientDissipation_nonneg (n + 1) (canonicalErrorCoeff ν hν a u n t)
  have hLcub := mul_le_mul_of_nonneg_right hL (pow_nonneg hD 3)
  have hBD := mul_le_mul_of_nonneg_right hB hD
  linarith

end

end MethbokeAddon.EhrenfestObstruction
