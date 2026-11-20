import QFA.Endpoints.Representation.Complexification
import QFA.Endpoints.Representation.EnergyProfile

/-!
# Native whole-space QFA: physical data and Leray--Hopf contracts

The spatial carrier is the actual full-volume Euclidean L2 space. Solenoidal
data are tested against every real smooth compactly supported scalar test;
there is no periodic, mean-zero, Schwartz, or smallness restriction.

The momentum equation uses every smooth compactly supported solenoidal
spacetime test whose support lies strictly in positive time. Its spatial
pairings and their time integrals are required to be genuinely integrable.
Iterated spatial-then-time integrals avoid imposing joint measurability on
the arbitrary representatives selected by the Lp coercion.

The Leray--Hopf predicate contains only the weak equation, weak derivatives,
initial equality, weak continuity, the standard energy classes and the
zero-start/almost-everywhere-start energy inequalities. It does not assume
existence, smoothness, comparison, continuation, or a QFA conclusion.
Pressure is eliminated by solenoidal tests; pressure reconstruction and
equivalence with a velocity--pressure formulation are separate obligations.

Prepared for matching external compilation and declaration-level audit.
No local Lean, Lake, or kernel execution is authorized by this file.
-/

set_option autoImplicit false
set_option Elab.async true

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Interval Topology

namespace MethbokeAddon.QuasiFeffermanA

/-- Euclidean three-space, with its Euclidean norm and full Lebesgue volume. -/
abbrev Space := QFA.Endpoints.Agmon.Space

/-- Actual real-vector L2 equivalence classes over all of R3. -/
abbrev SpatialL2 := QFA.Representation.RealSpatialL2

abbrev Velocity := ℝ → SpatialL2

abbrev WeakGradient := ℝ → Fin 3 → SpatialL2

/-- The j-th Euclidean coordinate direction. -/
def coordinateVector (j : Fin 3) : Space := EuclideanSpace.single j 1

/-- The actual gradient of a smooth scalar spatial test. -/
def scalarGradient (ψ : Space → ℝ) (x : Space) : Space :=
  WithLp.toLp 2 (fun j : Fin 3 => fderiv ℝ ψ x (coordinateVector j))

/-- Distributional divergence zero on the full spatial domain. Integrability
is explicit, so a totalized Bochner integral cannot make this condition vacuous. -/
def Solenoidal (v : SpatialL2) : Prop :=
  ∀ (ψ : Space → ℝ), ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
    Integrable (fun x : Space => inner ℝ (v x) (scalarGradient ψ x)) volume ∧
      (∫ x : Space, inner ℝ (v x) (scalarGradient ψ x)) = 0

/-- All solenoidal finite-energy whole-space data, with no smoothness premise. -/
abbrev EnergyDatum := {a : SpatialL2 // Solenoidal a}

/-- Three actual weak directional derivatives, in the coordinate directions.
The recovered compact-test derivative predicate uses every C-infinity compact
real scalar test and has full-volume L2 fields on both sides. -/
def SpatialWeakGradient (v : SpatialL2) (G : Fin 3 → SpatialL2) : Prop :=
  ∀ j : Fin 3,
    QFA.Endpoints.Representation.RealTestWeakDirectionalDerivative
      v (G j) (coordinateVector j)

/-- Genuine smooth compact positive-time solenoidal vector tests. -/
structure MomentumTest where
  value : ℝ × Space → Space
  smooth : ContDiff ℝ ∞ value
  compact_support : HasCompactSupport value
  positive_support : tsupport value ⊆ {z : ℝ × Space | 0 < z.1}
  solenoidal : ∀ (t : ℝ) (x : Space),
    (∑ j : Fin 3,
      (fderiv ℝ (fun y : Space => value (t, y)) x (coordinateVector j)) j) = 0

/-- Velocity paired with the actual time derivative of a momentum test. -/
def momentumTimeIntegrand (u : Velocity) (φ : MomentumTest)
    (t : ℝ) (x : Space) : ℝ :=
  inner ℝ (u t x) (fderiv ℝ (fun r : ℝ => φ.value (r, x)) t 1)

/-- The full convection contraction u_j u_i partial_j phi_i. -/
def momentumConvectionIntegrand (u : Velocity) (φ : MomentumTest)
    (t : ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, (u t x) j *
    inner ℝ (u t x)
      (fderiv ℝ (fun y : Space => φ.value (t, y)) x (coordinateVector j))

/-- The Frobenius gradient contraction partial_j u_i partial_j phi_i. -/
def momentumDissipationIntegrand (G : WeakGradient) (φ : MomentumTest)
    (t : ℝ) (x : Space) : ℝ :=
  ∑ j : Fin 3, inner ℝ (G t j x)
    (fderiv ℝ (fun y : Space => φ.value (t, y)) x (coordinateVector j))

/-- The unforced weak momentum equation with pressure eliminated by the
solenoidal tests. All three pairings are integrable before the equation is used. -/
structure WeakMomentum (ν : ℝ) (u : Velocity) (G : WeakGradient) : Prop where
  spatial_integrability : ∀ (φ : MomentumTest) (t : ℝ), 0 ≤ t →
    Integrable (momentumTimeIntegrand u φ t) volume ∧
      Integrable (momentumConvectionIntegrand u φ t) volume ∧
      Integrable (momentumDissipationIntegrand G φ t) volume
  time_integrability : ∀ φ : MomentumTest,
    Integrable (fun t : ℝ => ∫ x : Space, momentumTimeIntegrand u φ t x)
        (volume.restrict (Ioi (0 : ℝ))) ∧
      Integrable (fun t : ℝ => ∫ x : Space, momentumConvectionIntegrand u φ t x)
        (volume.restrict (Ioi (0 : ℝ))) ∧
      Integrable (fun t : ℝ => ∫ x : Space, momentumDissipationIntegrand G φ t x)
        (volume.restrict (Ioi (0 : ℝ)))
  equation : ∀ φ : MomentumTest,
    (∫ t in Ioi (0 : ℝ), ∫ x : Space, momentumTimeIntegrand u φ t x) +
        (∫ t in Ioi (0 : ℝ), ∫ x : Space, momentumConvectionIntegrand u φ t x) -
        ν * (∫ t in Ioi (0 : ℝ), ∫ x : Space, momentumDissipationIntegrand G φ t x) = 0

open QFA.Representation

/-- The standard energy inequality from one specified start to every later
upper endpoint. The start's nonnegativity is supplied separately. -/
def EnergyStart (ν : ℝ) (u : Velocity) (G : WeakGradient) (s : ℝ) : Prop :=
  ∀ r : ℝ, s ≤ r →
    velocityEnergy (u r) + 2 * ν * (∫ q in s..r, gradientEnergy (G q)) ≤
      velocityEnergy (u s)

/-- A physical whole-space Leray--Hopf energy class. Positivity of viscosity
is an explicit hypothesis of the analytic theorems, rather than a hidden type
restriction. The a.e. energy-start field is the usual strong energy inequality;
it assumes no restarted PDE membership or strong regularity. -/
structure LerayHopf (ν : ℝ) (a : SpatialL2)
    (u : Velocity) (G : WeakGradient) : Prop where
  momentum : WeakMomentum ν u G
  initial : u 0 = a
  solenoidal : ∀ t : ℝ, 0 ≤ t → Solenoidal (u t)
  velocity_aestronglyMeasurable : ∀ R : ℝ, 0 < R →
    AEStronglyMeasurable u (volume.restrict (Ioo (0 : ℝ) R))
  gradient_memLp : ∀ R : ℝ, 0 < R → ∀ j : Fin 3,
    MemLp (fun t => G t j) 2 (volume.restrict (Ioo (0 : ℝ) R))
  spatial_weak_gradient : ∀ R : ℝ, 0 < R →
    ∀ᵐ t ∂volume.restrict (Ioo (0 : ℝ) R), SpatialWeakGradient (u t) (G t)
  weak_continuity : ∀ b : SpatialL2,
    ContinuousOn (fun t => inner ℝ (u t) b) (Ici (0 : ℝ))
  energy_initial : ∀ t : ℝ, 0 ≤ t →
    velocityEnergy (u t) + 2 * ν * (∫ r in (0 : ℝ)..t, gradientEnergy (G r)) ≤
      velocityEnergy a
  energy_starts : ∀ R : ℝ, 0 < R →
    ∀ᵐ s ∂volume.restrict (Ioo (0 : ℝ) R), EnergyStart ν u G s

end MethbokeAddon.QuasiFeffermanA
