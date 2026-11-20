import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Scalar complex modal energy and damped uniqueness

These time-calculus endpoints apply to the actual coefficient derivatives
once the PDE/Fourier adapter has been supplied. The damped uniqueness
theorem needs no pressure reconstruction and no continuity of the phase
coefficient beyond the stated derivative and energy conditions.
-/

noncomputable section
open Set

namespace MethbokeAddon.FDSN

theorem complex_normSq_hasDerivAt {z : ℝ → ℂ} {dz : ℂ} {t : ℝ}
    (hz : HasDerivAt z dz t) :
    HasDerivAt (fun s => Complex.normSq (z s))
      (2 * (star (z t) * dz).re) t := by
  have hre : HasDerivAt (fun s => (z s).re) dz.re t :=
    Complex.reCLM.hasFDerivAt.comp_hasDerivAt t hz
  have him : HasDerivAt (fun s => (z s).im) dz.im t :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt t hz
  have hv : dz.re * (z t).re + (z t).re * dz.re +
      (dz.im * (z t).im + (z t).im * dz.im) =
      2 * (star (z t) * dz).re := by
    simp only [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  simpa only [Complex.normSq_apply, hv] using (hre.mul hre).add (him.mul him)

theorem complex_damped_normSq_hasDerivAt {z : ℝ → ℂ} {a : ℂ} {t : ℝ}
    (hz : HasDerivAt z (-a * z t) t) :
    HasDerivAt (fun s => Complex.normSq (z s))
      (-2 * a.re * Complex.normSq (z t)) t := by
  have hv : 2 * (star (z t) * (-a * z t)).re =
      -2 * a.re * Complex.normSq (z t) := by
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
      Complex.normSq_apply]
    ring
  simpa only [hv] using complex_normSq_hasDerivAt hz

theorem complex_damped_energy_antitone
    (z a : ℝ → ℂ) (s t : ℝ)
    (hc : ContinuousOn z (Icc s t))
    (hd : ∀ r ∈ Ioo s t, HasDerivAt z (-a r * z r) r)
    (ha : ∀ r ∈ Ioo s t, 0 ≤ (a r).re) :
    AntitoneOn (fun r => Complex.normSq (z r)) (Icc s t) := by
  refine antitoneOn_of_hasDerivWithinAt_nonpos
    (f' := fun r => -2 * (a r).re * Complex.normSq (z r))
    (convex_Icc s t) (Complex.continuous_normSq.comp_continuousOn hc) ?_ ?_
  · intro r hr
    have hr' : r ∈ Ioo s t := by simpa only [interior_Icc] using hr
    exact (complex_damped_normSq_hasDerivAt (hd r hr')).hasDerivWithinAt
  · intro r hr
    have hr' : r ∈ Ioo s t := by simpa only [interior_Icc] using hr
    have hp := mul_nonneg (ha r hr') (Complex.normSq_nonneg (z r))
    nlinarith

/-- A complex damped mode with zero initial value remains zero. -/
theorem complex_damped_zero_on_Icc
    (z a : ℝ → ℂ) (s t : ℝ) (hst : s ≤ t)
    (hc : ContinuousOn z (Icc s t))
    (hd : ∀ r ∈ Ioo s t, HasDerivAt z (-a r * z r) r)
    (ha : ∀ r ∈ Ioo s t, 0 ≤ (a r).re) (hz : z s = 0) :
    ∀ r ∈ Icc s t, z r = 0 := by
  have hanti := complex_damped_energy_antitone z a s t hc hd ha
  intro r hr
  have hle := hanti (show s ∈ Icc s t from ⟨le_rfl, hst⟩) hr hr.1
  apply Complex.normSq_eq_zero.mp
  apply le_antisymm
  · simpa only [hz, Complex.normSq_zero] using hle
  · exact Complex.normSq_nonneg (z r)

theorem complex_work_le_normSq (z f : ℂ) :
    2 * (star z * f).re ≤ Complex.normSq z + Complex.normSq f := by
  simp only [Complex.star_def, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.normSq_apply]
  nlinarith [sq_nonneg (z.re - f.re), sq_nonneg (z.im - f.im)]

/-- A real-energy-null nonlinear term contributes nothing to the modal
energy derivative; nonnegative damping can be discarded in an upper bound. -/
theorem complex_forced_energy_bound
    (z N f : ℂ) (d : ℝ) (hd : 0 ≤ d) (hN : (star z * N).re = 0) :
    2 * (star z * (-((d : ℂ) * z) - N + f)).re ≤
      Complex.normSq z + Complex.normSq f := by
  have he : 2 * (star z * (-((d : ℂ) * z) - N + f)).re =
      -2 * d * Complex.normSq z - 2 * (star z * N).re + 2 * (star z * f).re := by
    simp only [Complex.star_def, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, Complex.neg_re, Complex.neg_im,
      Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
    ring
  rw [he, hN]
  have hw := complex_work_le_normSq z f
  have hp := mul_nonneg hd (Complex.normSq_nonneg z)
  linarith

end MethbokeAddon.FDSN
