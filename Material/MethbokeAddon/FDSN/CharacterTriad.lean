import MethbokeAddon.FDSN.Phase
import SingularClosure.Galerkin

/-!
# Native integer-lattice translation characters and the FDSN correlation

This module uses the repository's actual unit-period Fourier character.
The spatial translation covariance of `datumFourierCoeff` is a separate
analytic adapter; these theorems establish the exact character algebra.
-/

noncomputable section

open SingularClosure
open scoped BigOperators ComplexConjugate

namespace MethbokeAddon.FDSN

/-- The real angle of the native unit-period character. -/
def characterAngle (k : Frequency) (x : Vec) : ℝ :=
  2 * Real.pi * ∑ i : Fin 3, (k i : ℝ) * x i

theorem fourierCharacter_eq_phase (k : Frequency) (x : Vec) :
    fourierCharacter k x = phase (characterAngle k x) := rfl

theorem characterAngle_add (k l : Frequency) (x : Vec) :
    characterAngle (k + l) x = characterAngle k x + characterAngle l x := by
  simp only [characterAngle, Pi.add_apply, Int.cast_add, add_mul,
    Finset.sum_add_distrib, mul_add]

theorem fourierCharacter_add_frequency (k l : Frequency) (x : Vec) :
    fourierCharacter (k + l) x = fourierCharacter k x * fourierCharacter l x := by
  simp only [fourierCharacter_eq_phase, characterAngle_add, phase_add]

/-- The correlation cancels every actual lattice translation character on
a resonant triad. -/
theorem triadCorrelation_native_character (k1 k2 k3 : Frequency)
    (htriad : k1 + k2 = k3) (x : Vec) (a b c : ℂ) :
    triadCorrelation (fourierCharacter k1 x * a)
      (fourierCharacter k2 x * b) (fourierCharacter k3 x * c) =
      triadCorrelation a b c := by
  subst k3
  simp only [fourierCharacter_eq_phase, characterAngle_add]
  exact triadCorrelation_translation a b c (characterAngle k1 x) (characterAngle k2 x)

/-- The discrete nontranslation obstruction: no spatial vector produces
native translation characters identifying distinct phase-family members
at a nonzero triad correlation. -/
theorem triad_phase_not_character_translation
    (k1 k2 k3 : Frequency) (htriad : k1 + k2 = k3)
    {a b c : ℂ} (hB : triadCorrelation a b c ≠ 0)
    {lambda eta : ℝ} (hlambda : |lambda| < Real.pi / 4)
    (heta : |eta| < Real.pi / 4) (hne : lambda ≠ eta) (x : Vec) :
    ¬ (fourierCharacter k1 x * a = a ∧
      fourierCharacter k2 x * b = b ∧
      fourierCharacter k3 x * (phase lambda * c) = phase eta * c) := by
  subst k3
  simp only [fourierCharacter_eq_phase, characterAngle_add]
  exact triad_phase_not_translation hB hlambda heta hne
    (characterAngle k1 x) (characterAngle k2 x)

end MethbokeAddon.FDSN
