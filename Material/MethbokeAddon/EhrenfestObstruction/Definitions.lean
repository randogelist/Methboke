import SingularClosure.CanonicalGalerkin
import SingularClosure.EnstrophyInequality

/-!
# Literal data and stopped drift for EHRENFEST-OBSTRUCTION

The family is the actual canonical Fourier--Galerkin family for one smooth
datum and one positive viscosity. The logical index `n` always represents
the physical cutoff `n + 1`. The stopped predicate contains only the explicit
coefficient drift, constants and the no-hit guard; it contains no regularity
or singularity conclusion.

Candidate source only. Matching external cached compilation and exact
type/axiom audits are required. No local Lean execution was performed.
-/

set_option autoImplicit false

open Set Filter SingularClosure

namespace MethbokeAddon.EhrenfestObstruction
noncomputable section

/-- Actual smooth periodic, solenoidal, mean-zero initial data. -/
abbrev SmoothDatum := {a : Field // SmoothSigmaZero a}

/-- The exact canonical Galerkin family, with strictly positive cutoff. -/
def canonicalFamily (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (n : ℕ) :
    GalerkinSolution ν a.val (n + 1) :=
  canonicalGalerkinSolution ν hν a.val a.property (n + 1)

/-- Half the physical gradient-square sum. -/
def halfEnstrophy (N : ℕ) (c : FourierCoeff) : ℝ :=
  coefficientDissipation N c / 2

/-- The bounded reciprocal observable when `eStar > 0`. -/
def reciprocalValue (eStar : ℝ) (N : ℕ) (c : FourierCoeff) : ℝ :=
  (1 + halfEnstrophy N c / eStar)⁻¹

/-- Literal reciprocal drift. The nonlinear-power sign is the native one:
`D' = -2 * ν * Z - 2 * P`, so the reciprocal rate has numerator `ν * Z + P`. -/
def reciprocalDrift (ν eStar : ℝ) (N : ℕ) (c : FourierCoeff) : ℝ :=
  (ν * coefficientLaplacianSquare N c +
      coefficientEnstrophyNonlinearPower N c) /
    (eStar * (1 + halfEnstrophy N c / eStar) ^ 2)

def canonicalEnstrophy (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (n : ℕ) (t : ℝ) : ℝ :=
  halfEnstrophy (n + 1) ((canonicalFamily ν hν a n).coeff t)

def canonicalReciprocal (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  reciprocalValue eStar (n + 1) ((canonicalFamily ν hν a n).coeff t)

def canonicalDrift (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar : ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  reciprocalDrift ν eStar (n + 1) ((canonicalFamily ν hν a n).coeff t)

/-- Strictly before the horizon, with every earlier point below threshold.
No first-hit time or existence of a hit is built into this definition. -/
def PreHit (e : ℝ → ℝ) (R T t : ℝ) : Prop :=
  0 ≤ t ∧ t < T ∧ ∀ s : ℝ, 0 ≤ s → s ≤ t → e s < R

/-- The one explicit stopped-drift premise for a fixed actual datum. -/
def StoppedForDatum (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (eStar gamma : ℝ) (R : ℕ → ℝ) : Prop :=
  0 < eStar ∧ 0 < gamma ∧ (∀ n : ℕ, 0 < R n) ∧
    Tendsto R atTop atTop ∧
      ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n → ∀ t : ℝ,
        PreHit (canonicalEnstrophy ν hν a n) (R n) (1 / gamma) t →
          canonicalDrift ν hν a eStar n t ≤ -gamma

/-- Existential dynamical assumption, not a global custom axiom. -/
def StoppedCommutatorBound (ν : ℝ) : Prop :=
  ∃ hν : 0 < ν, ∃ a : SmoothDatum, ∃ eStar gamma : ℝ, ∃ R : ℕ → ℝ,
    StoppedForDatum ν hν a eStar gamma R

/-- The actual universal smooth periodic NSE statement at viscosity `ν`. -/
def NSE_B (ν : ℝ) : Prop :=
  ∀ a : Field, SmoothSigmaZero a →
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P

end
end MethbokeAddon.EhrenfestObstruction
