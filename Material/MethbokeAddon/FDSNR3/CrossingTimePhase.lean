import MethbokeAddon.FDSN.TimeBump
import MethbokeAddon.FDSNR3.Contracts

/-!
# A signed compact time phase with a transverse interior zero

Multiplying a normalized bump by an affine factor preserves its support and
normalization, and creates a simple zero at a nearby nonvanishing Fourier
observation. This sharpens physical force separation to one common time.
No nonnegativity of the resulting phase is asserted or needed.
-/

set_option autoImplicit false

open Set Filter
open scoped ContDiff Topology

namespace MethbokeAddon.FDSNR3

noncomputable section

def crossingTimePhase (ρ : ℝ → ℝ) (tstar tzero : ℝ) (t : ℝ) : ℝ :=
  ((t - tzero) / (tstar - tzero)) * ρ t

@[simp] theorem crossingTimePhase_at_zero (ρ : ℝ → ℝ) (tstar tzero : ℝ) :
    crossingTimePhase ρ tstar tzero tzero = 0 := by
  simp [crossingTimePhase]

theorem crossingTimePhase_at_normalization {ρ : ℝ → ℝ} {tstar tzero : ℝ}
    (hρ : ρ tstar = 1) (hne : tzero ≠ tstar) :
    crossingTimePhase ρ tstar tzero tstar = 1 := by
  simp [crossingTimePhase, hρ, sub_ne_zero.mpr hne.symm]

theorem crossingTimePhase_contDiff {ρ : ℝ → ℝ}
    (hρ : ContDiff ℝ ∞ ρ) (tstar tzero : ℝ) :
    ContDiff ℝ ∞ (crossingTimePhase ρ tstar tzero) := by
  exact ((contDiff_id.sub contDiff_const).div_const (tstar - tzero)).mul hρ

theorem crossingTimePhase_tsupport_subset (ρ : ℝ → ℝ) (tstar tzero : ℝ) :
    tsupport (crossingTimePhase ρ tstar tzero) ⊆ tsupport ρ := by
  apply closure_mono
  intro t ht
  change ρ t ≠ 0
  intro hz
  exact ht (by simp [crossingTimePhase, hz])

theorem crossingTimePhase_hasCompactSupport {ρ : ℝ → ℝ}
    (hρ : HasCompactSupport ρ) (tstar tzero : ℝ) :
    HasCompactSupport (crossingTimePhase ρ tstar tzero) :=
  hρ.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (crossingTimePhase_tsupport_subset ρ tstar tzero)

theorem crossingTimePhase_hasDerivAt_zero {ρ : ℝ → ℝ}
    (hρ : Differentiable ℝ ρ) (tstar tzero : ℝ) :
    HasDerivAt (crossingTimePhase ρ tstar tzero)
      (ρ tzero / (tstar - tzero)) tzero := by
  have hlin : HasDerivAt (fun t : ℝ => (t - tzero) / (tstar - tzero))
      (1 / (tstar - tzero)) tzero :=
    ((hasDerivAt_id tzero).sub_const tzero).div_const (tstar - tzero)
  have hd : HasDerivAt (crossingTimePhase ρ tstar tzero)
      ((1 / (tstar - tzero)) * ρ tzero +
        ((tzero - tzero) / (tstar - tzero)) * deriv ρ tzero) tzero :=
    hlin.mul (hρ tzero).hasDerivAt
  simpa [div_eq_mul_inv, mul_comm] using hd

theorem crossingTimePhase_deriv_ne_zero {ρ : ℝ → ℝ}
    (hρ : Differentiable ℝ ρ) {tstar tzero : ℝ}
    (hne : tzero ≠ tstar) (hρzero : ρ tzero ≠ 0) :
    deriv (crossingTimePhase ρ tstar tzero) tzero ≠ 0 := by
  rw [(crossingTimePhase_hasDerivAt_zero hρ tstar tzero).deriv]
  exact div_ne_zero hρzero (sub_ne_zero.mpr hne.symm)

/-- A continuous nonzero scalar observation and a normalized bump remain
nonzero at a nearby distinct interior time. The direction chosen here is
to the right of the comparison time, but any such nearby time suffices. -/
theorem exists_nearby_nonzero_crossing_time
    {a b tstar : ℝ} (ha : a < tstar) (hb : tstar < b)
    {ρ : ℝ → ℝ} (hρ : ContinuousAt ρ tstar) (hρstar : ρ tstar = 1)
    {c : ℝ → ℂ} (hc : ContinuousAt c tstar) (hcstar : c tstar ≠ 0) :
    ∃ tzero ∈ Ioo a b, tzero ≠ tstar ∧ ρ tzero ≠ 0 ∧ c tzero ≠ 0 := by
  have hnρ : ∀ᶠ t in 𝓝 tstar, ρ t ≠ 0 :=
    hρ.eventually_ne (by simpa only [hρstar] using (one_ne_zero : (1 : ℝ) ≠ 0))
  have hnc : ∀ᶠ t in 𝓝 tstar, c t ≠ 0 :=
    hc.eventually_ne hcstar
  have hn : {t : ℝ | t ∈ Ioo a b ∧ ρ t ≠ 0 ∧ c t ≠ 0} ∈ 𝓝 tstar := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨ha, hb⟩, hnρ, hnc] with t ht hrt hct
    exact ⟨ht, hrt, hct⟩
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hn
  let tzero : ℝ := tstar + δ / 2
  have hmem : tzero ∈ Metric.ball tstar δ := by
    rw [Metric.mem_ball, Real.dist_eq]
    have heq : tzero - tstar = δ / 2 := by dsimp [tzero]; ring
    rw [heq, abs_of_pos (half_pos hδ)]
    exact half_lt_self hδ
  obtain ⟨ht, hrt, hct⟩ := hball hmem
  refine ⟨tzero, ht, ?_, hrt, hct⟩
  intro heq
  dsimp [tzero] at heq
  linarith

/-- The normalized interior bump supplies a signed time phase with a
nonzero slope at a common interior zero and a nonzero active observation.
The auxiliary cutoff is constructed explicitly, not assumed. -/
theorem exists_signed_crossing_time_phase
    {a b tstar : ℝ} (ha : a < tstar) (hb : tstar < b)
    {c : ℝ → ℂ} (hc : ContinuousAt c tstar) (hcstar : c tstar ≠ 0) :
    ∃ tzero : ℝ, ∃ β : ℝ → ℝ, ∃ slope : ℝ,
      tzero ∈ Ioo a b ∧ tzero ≠ tstar ∧ c tzero ≠ 0 ∧
      ContDiff ℝ ∞ β ∧ HasCompactSupport β ∧ tsupport β ⊆ Ioo a b ∧
      β tstar = 1 ∧ β tzero = 0 ∧ HasDerivAt β slope tzero ∧ slope ≠ 0 := by
  obtain ⟨ρ, hρsmooth, hρcompact, hρsupport, hρstar, _⟩ :=
    MethbokeAddon.FDSN.exists_normalized_time_bump ha hb
  obtain ⟨tzero, htzero, hne, hρzero, hczero⟩ :=
    exists_nearby_nonzero_crossing_time ha hb
      hρsmooth.continuous.continuousAt hρstar hc hcstar
  let β := crossingTimePhase ρ tstar tzero
  let slope := ρ tzero / (tstar - tzero)
  refine ⟨tzero, β, slope, htzero, hne, hczero,
    crossingTimePhase_contDiff hρsmooth tstar tzero,
    crossingTimePhase_hasCompactSupport hρcompact tstar tzero,
    (crossingTimePhase_tsupport_subset ρ tstar tzero).trans hρsupport,
    crossingTimePhase_at_normalization hρstar hne,
    crossingTimePhase_at_zero ρ tstar tzero, ?_, ?_⟩
  · exact crossingTimePhase_hasDerivAt_zero
      (hρsmooth.differentiable (by norm_num)) tstar tzero
  · exact div_ne_zero hρzero (sub_ne_zero.mpr hne.symm)

end

end MethbokeAddon.FDSNR3
