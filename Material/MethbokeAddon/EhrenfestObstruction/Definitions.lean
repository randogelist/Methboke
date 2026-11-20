import SingularClosure.CanonicalGalerkin
import SingularClosure.EnstrophyInequality

/-!
# Literal data and stopped drift for EHRENFEST-OBSTRUCTION

The family is the actual canonical Fourier--Galerkin family for one smooth
datum and one positive viscosity. The logical index `n` always represents
the physical cutoff `n + 1`. The stopped predicate contains only the explicit
coefficient drift, constants and the no-hit guard; it contains no regularity
or singularity conclusion.

Source-specific compiler/type/axiom evidence is recorded in the repository
registers. Physics commentary below does not add a formal premise.
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

/-- Existential dynamical assumption, not a global custom axiom.

Physicists' reason trace for the name and the precise hypothesis:

1. Start from a classical observable. At cutoff `N = n + 1`, the actual
   Galerkin coefficients follow a finite-dimensional ODE. The half-enstrophy
   `e = D / 2` measures gradient-square content, hence activity at small spatial
   scales. Growth of this quantity can coexist with decay of kinetic energy.
   With the native convention `D' = -2 * nu * Z - 2 * P`, write `W = -P`:
     e' = W - nu * Z.
   Here `W` is nonlinear enstrophy production and `nu * Z` is viscous loss.

2. Turn growth into a bounded observable. For a fixed `eStar > 0`, take
     v = (1 + e / eStar)^(-1),       0 < v <= 1.
   The scale `eStar` has enstrophy units; `v` is dimensionless. Large enstrophy
   means small `v`. `ReciprocalDrift.lean` derives the exact trajectory rate
     v' = (nu * Z + P) / (eStar * (1 + e / eStar)^2)
        = -(W - nu * Z) / (eStar * (1 + e / eStar)^2).
   Thus the assumed `v' <= -gamma` says that nonlinear production overcomes
   viscous loss by at least `gamma * eStar * (1 + e / eStar)^2`. It is a strong
   sustained-growth hypothesis; `gamma > 0` has inverse-time units.

3. Read that rate in Heisenberg/Ehrenfest language. For a time-independent
   observable A, the familiar quantum relation is
     d<A>/dt = <(i / hbar) [H, A]>,       [H, A] = H A - A H,
   when the evolution and operator domains justify it. For a classical phase
   vector field b, the corresponding formal transport expression is
     H = -i * hbar * (b . grad + z),      M_v psi = v * psi.
   The product rule gives `(i / hbar) [H, M_v] psi = (b . grad v) * psi`.
   In `CoreAlgebra.lean`, `normalized_hamiltonian_commutator` proves exactly
   this pointwise algebra for differentiable inputs. The multiplication term
   z cancels, and so does hbar. This motivates identifying the classical
   reciprocal rate with a normalized commutator; the Galerkin phase-space
   adapter and full Hilbert-space realization are separate obligations.

4. Viscosity does not require a volume-preserving phase flow. In a formal
   Koopman--von Neumann half-density description, `z = (div b) / 2` accounts
   for phase-space compression: `|psi|^2` obeys the continuity equation.
   With suitable boundary conditions this motivates a symmetric transport
   generator. It does not establish self-adjointness, domains or a unitary
   group here. This H generates transport of phase-space amplitudes; it is
   not being identified with the fluid's kinetic energy. The representation
   itself supplies neither quantization nor the negative drift inequality.

5. Explain "stopped" and the cutoff quantifiers. The inequality is required
   only for `0 <= t < 1 / gamma` while EVERY earlier time in `[0,t]` stays below
   `R n` (`PreHit`). No inequality after a threshold crossing is required.
   One fixed smooth datum, eStar and gamma must work for every sufficiently
   large cutoff, with `R n` tending to infinity. The constants cannot weaken
   with resolution. This uniformity is the substantive additional hypothesis;
   neither the commutator identity nor Ehrenfest's theorem provides it.

6. See the obstruction mechanism. A positive observable bounded above by 1
   cannot decrease at rate at least gamma throughout `[0, 1 / gamma]`.
   At a fixed cutoff the stopped alternative is threshold escape, not a
   singular finite-dimensional trajectory. A hypothetical global smooth NSE
   solution would give an eventual uniform Galerkin enstrophy bound on that
   slab. Choosing a sufficiently large n with `R n` above that bound keeps
   `PreHit` valid, so descent forces `v(1 / gamma) <= 0`, a contradiction.
   This is the conditional mechanism used in `DynamicalRoot.lean`.

The Lean predicate below is a scalar assertion along the canonical paths of
one datum, not an operator inequality for all states or an expectation bound.
Its witness remains unproved. The physics interpretation explains the form
of the assumption; it does not derive its existence from quantum mechanics.

Background for the interpretation (not premises of the Lean theorem):
* K. Peeters, Quantum Mechanics, section 20.2, Ehrenfest's theorem:
  https://www.maths.dur.ac.uk/users/kasper.peeters/mathphys/ehrenfest.html
* I. Joseph, Phys. Rev. Research 2, 043102 (2020), generalized Koopman--von
  Neumann transport, including non-Hamiltonian dynamics:
  https://arxiv.org/abs/2003.09980
-/
def StoppedCommutatorBound (ν : ℝ) : Prop :=
  ∃ hν : 0 < ν, ∃ a : SmoothDatum, ∃ eStar gamma : ℝ, ∃ R : ℕ → ℝ,
    StoppedForDatum ν hν a eStar gamma R

/-- The actual universal smooth periodic NSE statement at viscosity `ν`. -/
def NSE_B (ν : ℝ) : Prop :=
  ∀ a : Field, SmoothSigmaZero a →
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P

end
end MethbokeAddon.EhrenfestObstruction
