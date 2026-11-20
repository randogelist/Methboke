import MethbokeAddon.WeakFouriermanB.PhysicalEnstrophyEvolution
import MethbokeAddon.WeakFouriermanB.MaximalFrontRestriction
import SingularClosure.CubicBudget
import SingularClosure.UniformStrongBounds

/-!
Integrability of the actual physical enstrophy square on the whole open
interval gives one uniform H1 bound before the endpoint. Each closed
subinterval has the same integral bound, so physical cubic evolution and
the scalar integrating-factor theorem give a common enstrophy bound.
The Fourier-budget wrappers derive this physical integrability by Parseval.

No finite-endpoint value or regularity is used. The Fourier wrappers retain
the full extended Fourier sum of the actual slices as an explicit premise.
Prepared source only; external cached verification is required. No local
Lean, Lake, kernel audit or project test was executed.
-/

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure
open scoped ContDiff ENNReal Interval Topology

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- Full open-front budget of this exact maximal velocity, stopped at the
smaller of its extended lifetime and the finite physical cutoff. The minimum
is finite, so its real value is the actual endpoint of this open interval.
-/
def MaximalFourierBudgetFinite (u : Velocity) (Tmax : ℝ≥0∞) (cutoff : ℝ) : Prop :=
  FourierBudgetFinite (fun t => datumFourierCoeff (u t))
    (min Tmax (ENNReal.ofReal cutoff)).toReal

/-- Actual joint smoothness supplies measurability; actual physical slices
supply the full-series Parseval identity. No spectral equality is assumed.
-/
theorem initial_front_dissipation_square_integrable_of_fourier_budget
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T) :
    Integrable (fun t => physicalDissipation (u t) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) T)) := by
  have hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2)
      (localFrontSpacetime T) :=
    H.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
  apply homogeneous_dissipation_square_integrable_of_fourier_budget
    (volume.restrict (Ioo (0 : ℝ) T)) u ?_
    (local_physicalDissipation_aestronglyMeasurable u T hu) hbudget
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have hs := initial_front_smooth_slices ν T a u p H t ⟨ht.1.le, ht.2⟩
  exact ⟨hs.smooth, hs.periodic, hs.mean_zero⟩

/-- The actual physical enstrophy-square integral over the whole open front
controls enstrophy and accumulated Laplacian square at every earlier time.
The constant is shared by all closed subintervals approaching the endpoint.
-/
theorem initial_front_enstrophy_accumulation_of_dissipation_square
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) T))) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico (0 : ℝ) T,
      physicalDissipation (u t) +
        ν * (∫ s in (0 : ℝ)..t, physicalLaplacianSquare (u s)) ≤ B := by
  obtain ⟨C, hC, hcubic⟩ := INITIAL_FRONT_PHYSICAL_ENSTROPHY_CUBIC
  let M : ℝ := ∫ s in Ioo (0 : ℝ) T, physicalDissipation (u s) ^ 2
  have hM : 0 ≤ M := integral_nonneg (fun _ => sq_nonneg _)
  let B : ℝ := physicalDissipation (u 0) * Real.exp (C / ν ^ 3 * M)
  refine ⟨B, mul_nonneg (physical_dissipation_nonneg _) (Real.exp_pos _).le, ?_⟩
  intro t ht
  let b : ℝ := (t + T) / 2
  have hb : 0 ≤ b := by dsimp only [b]; linarith [ht.1]
  have htb : t ≤ b := by dsimp only [b]; linarith [ht.2]
  have hbT : b < T := by dsimp only [b]; linarith [ht.2]
  have hcont := initial_front_enstrophy_scalar_continuity ν T a u p H b hbT
  have hsub : Ioc (0 : ℝ) b ⊆ Ioo (0 : ℝ) T := by
    intro s hs
    exact ⟨hs.1, hs.2.trans_lt hbT⟩
  have hclosed : (∫ s in (0 : ℝ)..b, physicalDissipation (u s) ^ 2) ≤ M := by
    rw [intervalIntegral.integral_of_le hb]
    exact integral_mono_measure (Measure.restrict_mono_set volume hsub)
      (Eventually.of_forall (fun s => sq_nonneg (physicalDissipation (u s)))) hD
  have hscalar := CUBIC_ENERGY_OF_SQUARE_BUDGET_EXACT_INITIAL
    (y := fun s => physicalDissipation (u s))
    (z := fun s => Real.sqrt (physicalLaplacianSquare (u s)))
    (d := fun s => physicalEnstrophyRate ν (u s))
    (ν := ν) (κ := C / ν ^ 3) (T := b) (M := M)
    hν (div_nonneg hC.le (pow_nonneg hν.le _)) hb hM
    hcont.1 hcont.2.1 hcont.2.2
    (fun s _ => physical_dissipation_nonneg (u s))
    (fun s hs => (hcubic ν T hν a u p H s ⟨hs.1, hs.2.trans hbT⟩).1)
    (by
      intro s hs
      rw [Real.sq_sqrt (physicalLaplacianSquare_nonneg (u s))]
      exact (hcubic ν T hν a u p H s ⟨hs.1, hs.2.trans hbT⟩).2)
    hclosed
  have hzsq (s : ℝ) : Real.sqrt (physicalLaplacianSquare (u s)) ^ 2 =
      physicalLaplacianSquare (u s) :=
    Real.sq_sqrt (physicalLaplacianSquare_nonneg (u s))
  simpa only [B, hzsq] using hscalar t ⟨ht.1, htb⟩

/-- The full Fourier premise supplies the actual physical square budget
used by the accumulation theorem, with no separate enstrophy assumption.
-/
theorem initial_front_enstrophy_accumulation_of_fourier_budget
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p)
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ Ico (0 : ℝ) T,
      physicalDissipation (u t) +
        ν * (∫ s in (0 : ℝ)..t, physicalLaplacianSquare (u s)) ≤ B :=
  initial_front_enstrophy_accumulation_of_dissipation_square ν T a u p hν hT H
    (initial_front_dissipation_square_integrable_of_fourier_budget ν T a u p H hbudget)

/-- Poincare converts the derived enstrophy bound into a uniform bound for
the actual inhomogeneous physical H1 square, including the initial time.
-/
theorem initial_front_uniform_H1_of_dissipation_square
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p)
    (hD : Integrable (fun t => physicalDissipation (u t) ^ 2)
      (volume.restrict (Ioo (0 : ℝ) T))) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Ico (0 : ℝ) T, physicalH1Square (u t) ≤ R := by
  obtain ⟨B, hB, hb⟩ := initial_front_enstrophy_accumulation_of_dissipation_square
    ν T a u p hν hT H hD
  refine ⟨2 * B, by positivity, ?_⟩
  intro t ht
  have hZ : 0 ≤ ∫ s in (0 : ℝ)..t, physicalLaplacianSquare (u s) :=
    intervalIntegral.integral_nonneg_of_forall ht.1
      (fun s => physicalLaplacianSquare_nonneg (u s))
  have hD : physicalDissipation (u t) ≤ B := by
    have hνZ := mul_nonneg hν.le hZ
    linarith [hb t ht]
  have hs := initial_front_smooth_slices ν T a u p H t ht
  have hE := smooth_periodic_meanZero_energy_le_dissipation
    (u t) hs.smooth hs.periodic hs.mean_zero
  unfold physicalH1Square
  linarith

/-- The actual full Fourier budget yields the physical H1 bound through
the physical dissipation-square core, with no extra bound premise.
-/
theorem initial_front_uniform_H1_of_fourier_budget
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p)
    (hbudget : FourierBudgetFinite (fun t => datumFourierCoeff (u t)) T) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t ∈ Ico (0 : ℝ) T, physicalH1Square (u t) ≤ R :=
  initial_front_uniform_H1_of_dissipation_square ν T a u p hν hT H
    (initial_front_dissipation_square_integrable_of_fourier_budget ν T a u p H hbudget)

/-- The full budget through min(lifetime,cutoff) bounds the same actual
maximal trajectory on that entire half-open cap. In particular the constant
does not depend on how closely a closed subinterval approaches the cap.
-/
theorem maximal_front_uniform_H1_before_budget_cap
    (ν cutoff : ℝ) (a : Field) (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞)
    (hν : 0 < ν) (H : MaximalClassicalFront ν a u p Tmax)
    (hbudget : MaximalFourierBudgetFinite u Tmax cutoff) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ t : ℝ, 0 ≤ t →
      ENNReal.ofReal t < min Tmax (ENNReal.ofReal cutoff) →
      physicalH1Square (u t) ≤ R := by
  let cap : ℝ≥0∞ := min Tmax (ENNReal.ofReal cutoff)
  have hfinite : cap ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (min_le_right _ _)
  by_cases hcap : 0 < cap
  · let T : ℝ := cap.toReal
    have hT : 0 < T := ENNReal.toReal_pos hcap.ne' hfinite
    have hTmax : ENNReal.ofReal T ≤ Tmax := by
      rw [ENNReal.ofReal_toReal hfinite]
      exact min_le_left _ _
    have HF := maximal_classical_front_restrict_le ν T a u p Tmax H hT hTmax
    obtain ⟨R, hR, hb⟩ := initial_front_uniform_H1_of_fourier_budget
      ν T a u p hν hT HF hbudget
    refine ⟨R, hR, ?_⟩
    intro t ht htc
    exact hb t ⟨ht, (ENNReal.ofReal_lt_iff_lt_toReal ht hfinite).mp htc⟩
  · refine ⟨0, le_rfl, ?_⟩
    intro t ht htc
    have hc : cap ≤ 0 := le_of_not_gt hcap
    exact False.elim ((not_lt_of_ge (bot_le : (0 : ℝ≥0∞) ≤ ENNReal.ofReal t))
      (htc.trans_le hc))

end
end MethbokeAddon.WeakFouriermanB
