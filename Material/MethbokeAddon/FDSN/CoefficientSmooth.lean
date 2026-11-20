import MethbokeAddon.FDSN.Contracts
import MethbokeAddon.EhrenfestObstruction.ReferenceCoefficientEvolution

/-!
# All-order time smoothness of the actual Fourier coefficient

The native one-derivative cube-integration theorem is iterated.  Every time
derivative of the smooth preterminal physical field is again jointly smooth
on the open time cylinder, so no globally smooth extension through T is used.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped ContDiff

namespace MethbokeAddon.FDSN

open MethbokeAddon.WeakFouriermanB MethbokeAddon.EhrenfestObstruction

noncomputable section

theorem local_fourierCoeff_contDiffOn_nat (n : ℕ) (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (k : Frequency) (i : Fin 3) :
    ContDiffOn ℝ n (fun t : ℝ => datumFourierCoeff (u t) k i) (Ioo (0 : ℝ) T) := by
  induction n generalizing u with
  | zero =>
      apply contDiffOn_zero.mpr
      intro t ht
      exact (local_datumFourierCoeff_hasDerivAt u T hu k i t ht).continuousAt.continuousWithinAt
  | succ n ih =>
      simp only [Nat.cast_add, Nat.cast_one]
      rw [contDiffOn_succ_iff_deriv_of_isOpen isOpen_Ioo]
      refine ⟨?_, by simp, ?_⟩
      · intro t ht
        exact (local_datumFourierCoeff_hasDerivAt u T hu k i t ht).differentiableAt.differentiableWithinAt
      · apply (ih (timeDerivative u) (local_timeDerivative_contDiffOn u T hu)).congr
        intro t ht
        exact (local_datumFourierCoeff_hasDerivAt u T hu k i t ht).deriv

theorem local_fourierCoeff_contDiffOn (u : Velocity) (T : ℝ)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T))
    (k : Frequency) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : ℝ => datumFourierCoeff (u t) k i) (Ioo (0 : ℝ) T) := by
  rw [contDiffOn_infty]
  intro n
  exact local_fourierCoeff_contDiffOn_nat n u T hu k i

/-- Canonical Seed smoothness supplies the actual local coefficient API. -/
theorem Seed.fourierCoeff_contDiffOn {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) (k : Frequency) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : ℝ => datumFourierCoeff (u t) k i) (Ioo (0 : ℝ) T) :=
  local_fourierCoeff_contDiffOn u T
    (h.front.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)) k i

theorem Seed.fourierCoeff_contDiffOn_Icc {ν T a b : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) (ha : 0 < a) (hb : b < T)
    (k : Frequency) (i : Fin 3) :
    ContDiffOn ℝ ∞ (fun t : ℝ => datumFourierCoeff (u t) k i) (Icc a b) :=
  (h.fourierCoeff_contDiffOn k i).mono
    (fun t ht => ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩)

end

end MethbokeAddon.FDSN
