import MethbokeAddon.WeakFouriermanB.LocalCubicBarrier
import SingularClosure.StrongAccumulation
import SingularClosure.SobolevTrajectoryCalculus

/-!
Cutoff-uniform short-time bounds for the actual Fourier--Galerkin solutions.
The time depends only on viscosity and an upper bound for the initial
physical H1 seminorm squared. The actual Galerkin equation and the proved
cutoff-independent nonlinear estimate supply the cubic inequality.

No AX6, square-budget, compactness, physical local-solution or continuation
premise is introduced. This is the finite-dimensional estimate needed before
the separate physical local-existence construction.

Prepared for cached external verification. No local Lean execution.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped Interval

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

def galerkinEnstrophyConstant : ℝ :=
  Classical.choose GALERKIN_COEFFICIENT_ENSTROPHY_INEQUALITY

theorem galerkinEnstrophyConstant_pos : 0 < galerkinEnstrophyConstant :=
  (Classical.choose_spec GALERKIN_COEFFICIENT_ENSTROPHY_INEQUALITY).1

theorem galerkinEnstrophyConstant_bound
    (ν : ℝ) (hν : 0 < ν) (a : Field) (N : ℕ)
    (g : GalerkinSolution ν a N) (t : ℝ) (ht : 0 ≤ t) :
    ∃ d : ℝ,
      HasDerivWithinAt (fun r => coefficientDissipation N (g.coeff r)) d (Ici 0) t ∧
        d + ν * coefficientLaplacianSquare N (g.coeff t) ≤
          galerkinEnstrophyConstant / ν ^ 3 * (coefficientDissipation N (g.coeff t)) ^ 3 :=
  (Classical.choose_spec GALERKIN_COEFFICIENT_ENSTROPHY_INEQUALITY).2 ν hν a N g t ht

def localGalerkinTime (ν R : ℝ) : ℝ :=
  localCubicTime (galerkinEnstrophyConstant / ν ^ 3) R

def localGalerkinAccumulationBound (ν R : ℝ) : ℝ :=
  (R + 1) * Real.exp
    ((galerkinEnstrophyConstant / ν ^ 3) * (4 * (R + 1) ^ 2 * localGalerkinTime ν R))

theorem localGalerkinTime_pos {ν R : ℝ} (hν : 0 < ν) (hR : 0 ≤ R) :
    0 < localGalerkinTime ν R := by
  apply localCubicTime_pos _ hR
  exact div_nonneg galerkinEnstrophyConstant_pos.le (pow_nonneg hν.le _)

theorem localGalerkinAccumulationBound_nonneg {ν R : ℝ} (hR : 0 ≤ R) :
    0 ≤ localGalerkinAccumulationBound ν R := by
  unfold localGalerkinAccumulationBound
  positivity

/-- The enstrophy-rate expression is the derivative at every nonnegative
time, including the right derivative at zero. -/
theorem galerkin_local_cubic_inequality
    (ν : ℝ) (hν : 0 < ν) (a : Field) (N : ℕ)
    (g : GalerkinSolution ν a N) (t : ℝ) (ht : 0 ≤ t) :
    coefficientEnstrophyRate ν N (g.coeff t) +
        ν * coefficientLaplacianSquare N (g.coeff t) ≤
      galerkinEnstrophyConstant / ν ^ 3 * (coefficientDissipation N (g.coeff t)) ^ 3 := by
  obtain ⟨d, hd, hb⟩ := galerkinEnstrophyConstant_bound ν hν a N g t ht
  have hrate : HasDerivWithinAt
      (fun r => coefficientDissipation N (g.coeff r))
      (coefficientEnstrophyRate ν N (g.coeff t)) (Ici 0) t :=
    g.coefficientDissipation_hasDerivWithinAt ht
  have heq : coefficientEnstrophyRate ν N (g.coeff t) = d :=
    (hrate.derivWithin ((uniqueDiffOn_Ici 0) t ht)).symm.trans
      (hd.derivWithin ((uniqueDiffOn_Ici 0) t ht))
  simpa only [heq] using hb

/-- Actual finite Galerkin H1/H2 estimates on one common interval. The
initial higher Sobolev norms and the cutoff do not occur in its length or
in its bound. The square budget is derived, rather than supplied.
-/
theorem galerkin_uniform_local_enstrophy_accumulation
    (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (a : Field) (ha : SmoothSigmaZero a) (hinit : physicalDissipation a ≤ R) :
    ∀ (N : ℕ) (g : GalerkinSolution ν a N),
      ∀ t ∈ Icc (0 : ℝ) (localGalerkinTime ν R),
        coefficientDissipation N (g.coeff t) ≤ 2 * (R + 1) ∧
        coefficientDissipation N (g.coeff t) +
            ν * (∫ s in (0 : ℝ)..t, coefficientLaplacianSquare N (g.coeff s)) ≤
          localGalerkinAccumulationBound ν R := by
  intro N g
  let T : ℝ := localGalerkinTime ν R
  let κ : ℝ := galerkinEnstrophyConstant / ν ^ 3
  let y : ℝ → ℝ := fun t => coefficientDissipation N (g.coeff t)
  let z : ℝ → ℝ := fun t => Real.sqrt (coefficientLaplacianSquare N (g.coeff t))
  let d : ℝ → ℝ := fun t => coefficientEnstrophyRate ν N (g.coeff t)
  have hT : 0 ≤ T := (localGalerkinTime_pos hν hR).le
  have hκ : 0 ≤ κ :=
    div_nonneg galerkinEnstrophyConstant_pos.le (pow_nonneg hν.le _)
  have hy : ContinuousOn y (Icc 0 T) :=
    g.coefficientDissipation_continuousOn.mono (fun t ht => ht.1)
  have hz : ContinuousOn z (Icc 0 T) :=
    (Real.continuous_sqrt.comp_continuousOn
      g.coefficientLaplacianSquare_continuousOn).mono (fun t ht => ht.1)
  have hd : ContinuousOn d (Icc 0 T) :=
    g.coefficientEnstrophyRate_continuousOn.mono (fun t ht => ht.1)
  have hy0 : y 0 ≤ R := (g.coefficientDissipation_initial_le ha).trans hinit
  have hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ y t :=
    fun t _ => coefficientDissipation_nonneg N (g.coeff t)
  have hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt y (d t) (Ici 0) t :=
    fun t ht => g.coefficientDissipation_hasDerivWithinAt ht.1
  have hcubic : ∀ t ∈ Ico 0 T, d t + ν * (z t) ^ 2 ≤ κ * (y t) ^ 3 := by
    intro t ht
    dsimp only [z]
    rw [Real.sq_sqrt (coefficientLaplacianSquare_nonneg N (g.coeff t))]
    exact galerkin_local_cubic_inequality ν hν a N g t ht.1
  have hupper : ∀ t ∈ Ico 0 T, d t ≤ κ * (y t) ^ 3 := by
    intro t ht
    have hzpos := mul_nonneg hν.le (sq_nonneg (z t))
    linarith [hcubic t ht]
  have hpoint := cubic_short_time_barrier hκ hR hT le_rfl hy hy0 hderiv hupper
  have hacc := cubic_short_time_accumulation
    hν hκ hR hT le_rfl hy hz hd hnonneg hy0 hderiv hcubic
  have hzsq (s : ℝ) : (z s) ^ 2 = coefficientLaplacianSquare N (g.coeff s) :=
    Real.sq_sqrt (coefficientLaplacianSquare_nonneg N (g.coeff s))
  intro t ht
  refine ⟨hpoint t ht, ?_⟩
  simpa only [y, κ, T, localGalerkinAccumulationBound, hzsq] using hacc t ht

/-- The same uniform estimate expressed entirely by the actual physical
gradient and Laplacian integrals of the Galerkin velocity.
-/
theorem galerkin_uniform_local_physical_accumulation
    (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (a : Field) (ha : SmoothSigmaZero a) (hinit : physicalDissipation a ≤ R) :
    ∀ (N : ℕ) (g : GalerkinSolution ν a N),
      ∀ t ∈ Icc (0 : ℝ) (localGalerkinTime ν R),
        physicalDissipation (g.velocity t) ≤ 2 * (R + 1) ∧
        physicalDissipation (g.velocity t) +
            ν * (∫ s in (0 : ℝ)..t,
              ∫ x in unitCube, ‖laplacian (g.velocity s) x‖ ^ 2) ≤
          localGalerkinAccumulationBound ν R := by
  intro N g t ht
  obtain ⟨hpoint, hacc⟩ :=
    galerkin_uniform_local_enstrophy_accumulation ν R hν hR a ha hinit N g t ht
  have he : physicalDissipation (g.velocity t) = coefficientDissipation N (g.coeff t) :=
    g.physicalDissipation_eq ht.1
  have hZ : (∫ s in (0 : ℝ)..t,
      ∫ x in unitCube, ‖laplacian (g.velocity s) x‖ ^ 2) =
        ∫ s in (0 : ℝ)..t, coefficientLaplacianSquare N (g.coeff s) := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hs' : s ∈ Icc (0 : ℝ) t := by
      simpa only [uIcc_of_le ht.1] using hs
    exact finite_laplacian_integral_norm_sq N (g.coeff s) (g.real_symmetry s hs'.1)
  simpa only [he, hZ] using And.intro hpoint hacc

/-- The same interval supplies the literal H1 supremum and integrated H2
norm required by the high-order bootstrap, without a uniform AX6 premise.
-/
theorem galerkin_uniform_local_sobolev_bounds
    (ν R : ℝ) (hν : 0 < ν) (hR : 0 ≤ R)
    (a : Field) (ha : SmoothSigmaZero a) (hinit : physicalDissipation a ≤ R) :
    ∀ (N : ℕ) (g : GalerkinSolution ν a N),
      (∀ t ∈ Icc (0 : ℝ) (localGalerkinTime ν R),
        ‖g.sobolevState 1 t‖ ^ 2 ≤ 4 * (R + 1)) ∧
      IntervalIntegrable (fun t => ‖g.sobolevState 2 t‖ ^ 2)
        volume 0 (localGalerkinTime ν R) ∧
      (∫ t in (0 : ℝ)..(localGalerkinTime ν R), ‖g.sobolevState 2 t‖ ^ 2) ≤
        6 * (R + 1) * localGalerkinTime ν R + localGalerkinAccumulationBound ν R / ν := by
  intro N g
  let T : ℝ := localGalerkinTime ν R
  have hT : 0 ≤ T := (localGalerkinTime_pos hν hR).le
  have hb := galerkin_uniform_local_enstrophy_accumulation ν R hν hR a ha hinit N g
  have hiH2 : IntervalIntegrable (fun t => ‖g.sobolevState 2 t‖ ^ 2) volume 0 T :=
    (((g.sobolevState_continuousOn 2).mono (fun t ht => ht.1)).norm.pow 2).intervalIntegrable_of_Icc hT
  have hiZ : IntervalIntegrable
      (fun t => coefficientLaplacianSquare N (g.coeff t)) volume 0 T :=
    (g.coefficientLaplacianSquare_continuousOn.mono
      (fun t ht => ht.1)).intervalIntegrable_of_Icc hT
  have hZ : (∫ t in (0 : ℝ)..T, coefficientLaplacianSquare N (g.coeff t)) ≤
      localGalerkinAccumulationBound ν R / ν := by
    have hacc := (hb T ⟨hT, le_rfl⟩).2
    have hD := coefficientDissipation_nonneg N (g.coeff T)
    apply (le_div_iff₀ hν).2
    nlinarith
  refine ⟨?_, hiH2, ?_⟩
  · intro t ht
    change ‖finiteSobolev 1 N (g.coeff t)‖ ^ 2 ≤ _
    rw [finiteSobolev_H1_norm_sq]
    have hD := (hb t ht).1
    have hE := coefficientEnergy_le_dissipation N (g.coeff t)
    linarith
  · calc
      (∫ t in (0 : ℝ)..T, ‖g.sobolevState 2 t‖ ^ 2) ≤
          ∫ t in (0 : ℝ)..T, 6 * (R + 1) + coefficientLaplacianSquare N (g.coeff t) := by
        apply intervalIntegral.integral_mono_on hT hiH2 (intervalIntegrable_const.add hiZ)
        intro t ht
        change ‖finiteSobolev 2 N (g.coeff t)‖ ^ 2 ≤ _
        rw [finiteSobolev_H2_norm_sq]
        have hD := (hb t ht).1
        have hE := coefficientEnergy_le_dissipation N (g.coeff t)
        linarith
      _ = 6 * (R + 1) * T +
          ∫ t in (0 : ℝ)..T, coefficientLaplacianSquare N (g.coeff t) := by
        rw [intervalIntegral.integral_add intervalIntegrable_const hiZ,
          intervalIntegral.integral_const]
        simp only [sub_zero, smul_eq_mul]
        ring
      _ ≤ 6 * (R + 1) * T + localGalerkinAccumulationBound ν R / ν :=
        add_le_add le_rfl hZ

end

end MethbokeAddon.WeakFouriermanB
