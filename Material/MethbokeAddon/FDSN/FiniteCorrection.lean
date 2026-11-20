import MethbokeAddon.FDSN.PhysicalPair

/-!
# The Fourier rotation is an explicit finite physical correction

This identity removes the infinite series from the parameter/time-smoothness
step.  The correction contains only the chosen coefficient and one character.
-/

set_option autoImplicit false

open Set MeasureTheory
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

open SingularClosure

noncomputable section

theorem scalarFourierSeries_pairRotate {a : Frequency} (ha : a ≠ 0)
    (z : ℂ) (c : FourierCoeff) (i : Fin 3)
    (hc : Summable (fun k => ‖c k i‖)) (x : Vec) :
    scalarFourierSeries (fun k => pairRotate a z c k i) x =
      scalarFourierSeries (fun k => c k i) x +
        fourierCharacter a x * ((z - 1) * c a i) +
        fourierCharacter (-a) x * ((star z - 1) * c (-a) i) := by
  classical
  apply HasSum.tsum_eq
  have hbase := (scalarFourierSeries_summable hc x).hasSum
  have hpos := hasSum_ite_eq a (fourierCharacter a x * ((z - 1) * c a i))
  have hneg := hasSum_ite_eq (-a)
    (fourierCharacter (-a) x * ((star z - 1) * c (-a) i))
  apply ((hbase.add hpos).add hneg).congr
  intro S
  apply Finset.sum_congr rfl
  intro k hkS
  by_cases hk : k = a
  · subst k
    simp [pairRotate, pairMultiplier, frequency_ne_neg_self ha] <;> ring
  · by_cases hkn : k = -a
    · subst k
      simp [pairRotate, pairMultiplier, Ne.symm (frequency_ne_neg_self ha)] <;> ring
    · simp [pairRotate, pairMultiplier, hk, hkn]

/-- The literal finite correction at a spatial point. -/
def physicalPairCorrection (a : Frequency) (z : ℂ) (v : Field) : Field :=
  fun x => WithLp.toLp 2 (fun i : Fin 3 =>
    2 * (fourierCharacter a x * ((z - 1) * datumFourierCoeff v a i)).re)

theorem physicalPairCorrection_one (a : Frequency) (v : Field) :
    physicalPairCorrection a 1 v = 0 := by
  funext x
  ext i
  simp [physicalPairCorrection]

theorem physicalPairCorrection_smooth (a : Frequency) (z : ℂ) (v : Field) :
    ContDiff ℝ ∞ (physicalPairCorrection a z v) := by
  apply (contDiff_piLp 2).2
  intro i
  exact contDiff_const.mul
    (Complex.reCLM.contDiff.comp ((fourierCharacter_contDiff a).mul contDiff_const))

theorem physicalPairCorrection_periodic (a : Frequency) (z : ℂ) (v : Field) :
    SpatialPeriodic (physicalPairCorrection a z v) := by
  intro x j
  ext i
  change 2 * (fourierCharacter a (x + unitVector j) *
      ((z - 1) * datumFourierCoeff v a i)).re =
    2 * (fourierCharacter a x * ((z - 1) * datumFourierCoeff v a i)).re
  rw [fourierCharacter_periodic]

/-- A literal two-mode correction equals the actual Fourier-rotated field.
The identity holds for every complex multiplier, not only unit phases. -/
theorem physicalPairRotation_eq_add_correction {a : Frequency} (ha : a ≠ 0)
    (z : ℂ) {v : Field} (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    physicalPairRotation a z v = v + physicalPairCorrection a z v := by
  funext x
  ext i
  have hr := smoothPeriodic_fourier_rapid hv hp i
  have hscalar := scalarFourierSeries_pairRotate ha z (datumFourierCoeff v) i
    hr.summable_norm x
  have hrepr : scalarFourierSeries (fun k => datumFourierCoeff v k i) x =
      (v x i : ℂ) := by
    rw [scalarFourierSeries_eq_smoothFourierSynthesis_component
      (datumFourierCoeff v) (datumFourierCoeff_reality v) i x,
      smoothPeriodic_fourier_reconstruction hv hp]
  have hneg : star (fourierCharacter a x) *
      ((star z - 1) * star (datumFourierCoeff v a i)) =
      star (fourierCharacter a x * ((z - 1) * datumFourierCoeff v a i)) := by
    simp only [star_mul, star_sub, star_one]
    ring
  change (scalarFourierSeries (fun k => pairRotate a z (datumFourierCoeff v) k i) x).re =
    v x i + 2 * (fourierCharacter a x * ((z - 1) * datumFourierCoeff v a i)).re
  rw [hscalar, fourierCharacter_neg, (datumFourierCoeff_reality v) a i, hneg, hrepr]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.star_def, Complex.conj_re]
  ring

/-- A compact time phase acts through a finite explicit correction of the
actual velocity; this is the spatial algebra needed before proving joint
time smoothness of the selected coefficient. -/
theorem PHYSICAL_PAIR_ROTATION_IS_FINITE_CORRECTION
    {a : Frequency} (ha : a ≠ 0) (z : ℂ) {v : Field}
    (hv : ContDiff ℝ ∞ v) (hp : SpatialPeriodic v) :
    physicalPairRotation a z v - v = physicalPairCorrection a z v := by
  rw [physicalPairRotation_eq_add_correction ha z hv hp]
  abel

end

end MethbokeAddon.FDSN
