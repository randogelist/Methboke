import MethbokeAddon.FDSN.PhysicalPair
import MethbokeAddon.FDSN.Contracts

/-!
# An actual pointwise velocity bound from a common summable Fourier envelope

The weight includes the zero mode. This is an infinite-series estimate for
the actual smooth periodic field, with no mean-zero or cutoff hypothesis.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

noncomputable section

def torusEnvelopeMass : ℝ :=
  ∑' k : Frequency, (torusSobolevWeight k)⁻¹ ^ 4

theorem torusEnvelopeMass_nonneg : 0 ≤ torusEnvelopeMass :=
  tsum_nonneg (fun k => by positivity)

theorem smoothPeriodic_exists_fourier_envelope {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff v k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4 := by
  refine ⟨smoothDatumDecayConstant 2 v, smoothDatumDecayConstant_nonneg 2 v, ?_⟩
  intro k i
  have hb := smooth_datum_sobolev_decay 2 v hv hp k i
  have hw : 0 < torusSobolevWeight k ^ 4 := pow_pos (torusSobolevWeight_pos k) 4
  have he : ‖datumFourierCoeff v k i‖ ≤
      smoothDatumDecayConstant 2 v / torusSobolevWeight k ^ 4 := by
    apply (le_div_iff₀ hw).mpr
    simpa only [Nat.reduceAdd, mul_comm] using hb
  simpa only [div_eq_mul_inv, inv_pow] using he

theorem component_bound_of_fourier_envelope {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) (C : ℝ)
    (hc : ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff v k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4)
    (x : Vec) (i : Fin 3) : ‖v x i‖ ≤ C * torusEnvelopeMass := by
  have hsum : HasSum (fun k : Frequency => C * (torusSobolevWeight k)⁻¹ ^ 4)
      (C * torusEnvelopeMass) :=
    summable_torusSobolevWeight_inv_four.hasSum.mul_left C
  have hbound : ‖scalarFourierSeries (fun k => datumFourierCoeff v k i) x‖ ≤
      C * torusEnvelopeMass := by
    apply tsum_of_norm_bounded hsum
    intro k
    simpa only [norm_mul, fourierCharacter_norm, one_mul] using hc k i
  rw [scalarFourierSeries_eq_smoothFourierSynthesis_component
    (datumFourierCoeff v) (datumFourierCoeff_reality v) i x,
    smoothPeriodic_fourier_reconstruction hv hp] at hbound
  simpa only [Complex.norm_real] using hbound

/-- A deliberately nonsharp constant suffices for the terminal contradiction. -/
theorem pointwise_bound_of_fourier_envelope {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) {C : ℝ} (hC : 0 ≤ C)
    (hc : ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff v k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4)
    (x : Vec) : ‖v x‖ ≤ 3 * (C * torusEnvelopeMass) := by
  have hb : 0 ≤ C * torusEnvelopeMass := mul_nonneg hC torusEnvelopeMass_nonneg
  have hs : ‖v x‖ ^ 2 ≤ 3 * (C * torusEnvelopeMass) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc
      _ ≤ ∑ i : Fin 3, (C * torusEnvelopeMass) ^ 2 :=
        Finset.sum_le_sum (fun i _ =>
          pow_le_pow_left₀ (norm_nonneg _) (component_bound_of_fourier_envelope hv hp C hc x i) 2)
      _ = 3 * (C * torusEnvelopeMass) ^ 2 := by simp
  apply (sq_le_sq₀ (norm_nonneg (v x)) (mul_nonneg (by norm_num) hb)).mp
  nlinarith [sq_nonneg (C * torusEnvelopeMass)]

/-- The final contradiction for the active-triad argument: an admitted seed
cannot have a common summable coefficient envelope on any terminal interval. -/
theorem Seed.no_final_uniform_fourier_envelope {ν T : ℝ} {u F : Velocity}
    {p : Pressure} (h : Seed ν T u p F) (s : ℝ) (hs : s ∈ Ico (0 : ℝ) T) :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Ioo s T, ∀ k : Frequency, ∀ i : Fin 3,
      ‖datumFourierCoeff (u t) k i‖ ≤ C * (torusSobolevWeight k)⁻¹ ^ 4 := by
  rintro ⟨C, hC, henv⟩
  have hB : 0 ≤ 3 * (C * torusEnvelopeMass) :=
    mul_nonneg (by norm_num) (mul_nonneg hC torusEnvelopeMass_nonneg)
  obtain ⟨t, ht, x, hx, hlarge⟩ := h.terminal_blowup s hs
    (3 * (C * torusEnvelopeMass)) hB
  have ht0 : t ∈ Ico (0 : ℝ) T := ⟨le_trans hs.1 ht.1.le, ht.2⟩
  have hv : ContDiff ℝ ∞ (u t) := by
    simpa only [Function.comp_def, id_eq] using h.front.velocity_smooth.comp_contDiff
      (contDiff_const.prodMk contDiff_id) (fun _ => ht0)
  have hbound := pointwise_bound_of_fourier_envelope hv
    (h.front.velocity_periodic t ht0) hC (henv t ht) x
  exact (not_lt_of_ge hbound) hlarge

end

end MethbokeAddon.FDSN
