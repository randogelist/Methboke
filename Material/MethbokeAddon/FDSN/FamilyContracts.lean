import MethbokeAddon.FDSN.Contracts
import SingularClosure.LerayL2Contraction
import SingularClosure.SmoothDatumSobolev
import Mathlib.LinearAlgebra.CrossProduct

/-!
# The canonical FDSN family with shared witnesses

The five clauses use the same interval `(a,b)`, comparison time, parameter
radius, velocity family, and force family. The helical coefficient is the
literal Hermitian coordinate in a fixed helical frame. The implementation
can prove the stronger conclusion for every frame array; the canonical
`Family` quantifies genuine orthonormal curl-eigenframes explicitly.

The C^r convention is the sum of the suprema of the actual full time-space
Fréchet derivatives through order r on the compact unit-cell slab.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped BigOperators ContDiff

namespace MethbokeAddon.FDSN

noncomputable section

abbrev HelicalFrameArray := Frequency → Fin 2 → Fin 3 → ℂ

def helicitySign (σ : Fin 2) : ℝ := if σ = 0 then 1 else -1

def frequencyLength (k : Frequency) : ℝ :=
  Real.sqrt (∑ i : Fin 3, (k i : ℝ) ^ 2)

/-- The actual Fourier symbol of curl, including the unit-torus factor 2π. -/
def helicalCurl (k : Frequency) (v : Fin 3 → ℂ) : Fin 3 → ℂ :=
  fun i => (2 * (Real.pi : ℂ) * Complex.I) *
    crossProduct (fun j : Fin 3 => (k j : ℂ)) v i

/-- The fixed frame conventions in canonical FDSN. Values at frequency zero
are irrelevant; the zero mode is preserved separately. -/
def IsHelicalFrame (h : HelicalFrameArray) : Prop :=
  (∀ k : Frequency, k ≠ 0 → ∀ σ τ : Fin 2,
    (∑ i : Fin 3, star (h k σ i) * h k τ i) = if σ = τ then 1 else 0) ∧
  (∀ k : Frequency, k ≠ 0 → ∀ σ : Fin 2, ∀ i : Fin 3,
    helicalCurl k (h k σ) i =
      ((helicitySign σ * (2 * Real.pi) * frequencyLength k : ℝ) : ℂ) * h k σ i) ∧
  (∀ k : Frequency, k ≠ 0 → ∀ σ : Fin 2, ∀ i : Fin 3,
    h (-k) σ i = star (h k σ i))

def helicalObservation (h : Fin 3 → ℂ) : (Fin 3 → ℂ) →ₗ[ℂ] ℂ where
  toFun v := ∑ i : Fin 3, star (h i) * v i
  map_add' v w := by simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c v := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring

def helicalCoefficient (h : HelicalFrameArray) (v : Field)
    (k : Frequency) (σ : Fin 2) : ℂ :=
  helicalObservation (h k σ) (datumFourierCoeff v k)

def CompactTemporalCorrection (a b : ℝ) (V : Velocity) : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × Vec => V z.1 z.2) ∧
  (∀ t : ℝ, SpatialPeriodic (V t)) ∧
  HasCompactSupport V ∧ tsupport V ⊆ Ioo a b

def spacetimeCrNorm (r : ℕ) (a b : ℝ) (V : Velocity) : ℝ :=
  ∑ n ∈ Finset.range (r + 1),
    sSup ((fun z : ℝ × Vec =>
      ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => V y.1 y.2) z‖) ''
        (Icc a b ×ˢ unitCube))

def ExactRealizationAndAgreement (ν T a b ε : ℝ)
    (u : Velocity) (p : Pressure) (F : Velocity)
    (U G : ℝ → Velocity) : Prop :=
  ∀ λ : ℝ, |λ| < ε →
    PreterminalNSE ν T (U λ) p (G λ) ∧
    MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce (G λ) ∧
    U λ 0 = u 0 ∧
    CompactTemporalCorrection a b (U λ - u) ∧
    CompactTemporalCorrection a b (G λ - F) ∧
    CofinalVelocityBlowup T (U λ)

def CompleteHelicalPowerPreservation (h : HelicalFrameArray)
    (T ε : ℝ) (u : Velocity) (U : ℝ → Velocity) : Prop :=
  ∀ λ : ℝ, |λ| < ε → ∀ t ∈ Ico (0 : ℝ) T,
    (∀ k : Frequency, k ≠ 0 → ∀ σ : Fin 2,
      Complex.normSq (helicalCoefficient h (U λ t) k σ) =
        Complex.normSq (helicalCoefficient h (u t) k σ)) ∧
    datumFourierCoeff (U λ t) 0 = datumFourierCoeff (u t) 0

def TranslationSeparation (tstar ε : ℝ) (U : ℝ → Velocity) : Prop :=
  ∀ λ η : ℝ, |λ| < ε → |η| < ε → λ ≠ η →
    ¬ ∃ y : Vec, ∀ x : Vec, U λ tstar x = U η tstar (x + y)

/-- A literal unequal coefficient of the actual periodic Leray-projected
force histories, retaining frequency zero. Linearity makes this exactly a
nonzero coefficient of the projected force difference. -/
def ProjectedForceSeparation (T ε : ℝ) (G : ℝ → Velocity) : Prop :=
  ∀ λ η : ℝ, |λ| < ε → |η| < ε → λ ≠ η →
    ∃ t ∈ Ico (0 : ℝ) T, ∃ k : Frequency, ∃ i : Fin 3,
      coefficientLeray k (datumFourierCoeff (G λ t) k) i ≠
        coefficientLeray k (datumFourierCoeff (G η t) k) i

def SmoothSmallness (a b ε : ℝ) (u F : Velocity)
    (U G : ℝ → Velocity) : Prop :=
  ∀ r : ℕ, ∃ C δ : ℝ, 0 ≤ C ∧ 0 < δ ∧
    ∀ λ : ℝ, |λ| < min ε δ →
      spacetimeCrNorm r a b (U λ - u) +
        spacetimeCrNorm r a b (G λ - F) ≤ C * |λ|

/-- FDSN.1--FDSN.5 for a prescribed array of helical coordinate vectors. -/
def FamilyFor (h : HelicalFrameArray) (ν T : ℝ)
    (u : Velocity) (p : Pressure) (F : Velocity) : Prop :=
  ∀ s ∈ Ico (0 : ℝ) T,
    ∃ a b tstar ε : ℝ, ∃ U G : ℝ → Velocity,
      s < a ∧ a < b ∧ b < T ∧ tstar ∈ Ioo a b ∧ 0 < ε ∧
      U 0 = u ∧ G 0 = F ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
        (U q.1 - u) q.2.1 q.2.2) {q | |q.1| < ε} ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
        (G q.1 - F) q.2.1 q.2.2) {q | |q.1| < ε} ∧
      ExactRealizationAndAgreement ν T a b ε u p F U G ∧
      CompleteHelicalPowerPreservation h T ε u U ∧
      TranslationSeparation tstar ε U ∧
      ProjectedForceSeparation T ε G ∧
      SmoothSmallness a b ε u F U G

/-- The unparameterized canonical target. Each genuine fixed helical frame
receives the one common family required by all five clauses. -/
def Family (ν T : ℝ) (u : Velocity) (p : Pressure) (F : Velocity) : Prop :=
  ∀ h : HelicalFrameArray, IsHelicalFrame h → FamilyFor h ν T u p F

theorem family_of_all_frame_arrays {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (H : ∀ h : HelicalFrameArray, FamilyFor h ν T u p F) :
    Family ν T u p F := fun h _ => H h

theorem Family.for_fixed_helical_frame {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (H : Family ν T u p F) {h : HelicalFrameArray} (hh : IsHelicalFrame h) :
    FamilyFor h ν T u p F := H h hh

end

end MethbokeAddon.FDSN
