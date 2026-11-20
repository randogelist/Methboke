import SingularClosure.Contracts
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Actual whole-space FDSN contracts

The physical fields and differential operators are the native Euclidean ones.
There is no periodicity assumption. Schwartz regularity is expressed by
actual weighted derivative bounds, since Schwartz space is not normable.
At the initial boundary the derivatives are within the preterminal domain.
The seed contains no family witness or spectral/separation conclusion.

Prepared without local Lean execution. Acceptance requires matching external
compiler and theorem-level type/axiom evidence.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure
open scoped BigOperators ContDiff FourierTransform

namespace MethbokeAddon.FDSNR3

noncomputable section

abbrev CVec := EuclideanSpace ℂ (Fin 3)

def complexify (v : Vec) : CVec :=
  WithLp.toLp 2 (fun i : Fin 3 => (v i : ℂ))

def realify (v : CVec) : Vec :=
  WithLp.toLp 2 (fun i : Fin 3 => (v i).re)

def preterminalSpacetime (T : ℝ) : Set (ℝ × Vec) :=
  {z | z.1 ∈ Ico (0 : ℝ) T}

/-- Weighted full time-space derivative; equivalent to the finite collection
of mixed coordinate derivatives of this order. -/
def weightedJet (N n : ℕ) (V : Velocity) (z : ℝ × Vec) : ℝ :=
  (1 + ‖z.2‖) ^ N *
    ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => V y.1 y.2) z‖

/-- The one-sided version used for the seed at time zero. -/
def weightedJetWithin (T : ℝ) (N n : ℕ) (V : Velocity)
    (z : ℝ × Vec) : ℝ :=
  (1 + ‖z.2‖) ^ N *
    ‖iteratedFDerivWithin ℝ n (fun y : ℝ × Vec => V y.1 y.2)
      (preterminalSpacetime T) z‖

/-- All orders have their own finite bound, uniformly in time and space. -/
def GlobalSchwartzBounds (V : Velocity) : Prop :=
  ∀ N n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × Vec, weightedJet N n V z ≤ C

/-- Literal local-Schwartz regularity on every compact preterminal slab.
No bound uniform up to the singular time is required. -/
def LocalSchwartz (T : ℝ) (V : Velocity) : Prop :=
  ContDiffOn ℝ ∞ (fun z : ℝ × Vec => V z.1 z.2) (preterminalSpacetime T) ∧
  ∀ b ∈ Ico (0 : ℝ) T, ∀ N n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
    ∀ t ∈ Icc (0 : ℝ) b, ∀ x : Vec, weightedJetWithin T N n V (t, x) ≤ C

/-- Smooth force with positive compact time support and all spatial
rapid-decay bounds, including its mixed derivatives. -/
structure AdmissibleForce (F : Velocity) : Prop where
  smooth : ContDiff ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2)
  schwartz_bounds : GlobalSchwartzBounds F
  time_support : ∃ a b : ℝ, 0 < a ∧ a < b ∧
    ∀ t : ℝ, t ∉ Icc a b → F t = 0

structure PreterminalNSE (ν T : ℝ) (u : Velocity) (p : Pressure)
    (F : Velocity) : Prop where
  velocity_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (preterminalSpacetime T)
  pressure_smooth :
    ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) (preterminalSpacetime T)
  divergence_free : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0
  equation : ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
    timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
      ν • laplacian (u t) x + F t x

def BoundedEnergy (T : ℝ) (u : Velocity) : Prop :=
  ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Ico (0 : ℝ) T,
    Integrable (fun x : Vec => ‖u t x‖ ^ 2) volume ∧
      (∫ x : Vec, ‖u t x‖ ^ 2) ≤ E

def gradientSquare (v : Field) (x : Vec) : ℝ :=
  ∑ i : Fin 3, ‖coordinateDerivative v i x‖ ^ 2

def dissipation (v : Field) : ℝ := ∫ x : Vec, gradientSquare v x

def FiniteDissipation (T : ℝ) (u : Velocity) : Prop :=
  (∀ t ∈ Ico (0 : ℝ) T, Integrable (gradientSquare (u t)) volume) ∧
    IntegrableOn (fun t => dissipation (u t)) (Ioo (0 : ℝ) T) volume

/-- The same compact set witnesses cofinal physical velocity blowup. -/
def CompactLocalBlowup (T : ℝ) (u : Velocity) : Prop :=
  ∃ K : Set Vec, IsCompact K ∧
    ∀ s ∈ Ico (0 : ℝ) T, ∀ M : ℝ, 0 ≤ M →
      ∃ t ∈ Ioo s T, ∃ x ∈ K, M < ‖u t x‖

structure Seed (ν T : ℝ) (u : Velocity) (p : Pressure)
    (F : Velocity) : Prop where
  viscosity_pos : 0 < ν
  terminal_pos : 0 < T
  front : PreterminalNSE ν T u p F
  local_schwartz : LocalSchwartz T u
  force : AdmissibleForce F
  bounded_energy : BoundedEnergy T u
  finite_dissipation : FiniteDissipation T u
  terminal_blowup : CompactLocalBlowup T u

/-- The literal whole-space Fourier transform with the library 2π convention. -/
def fourierVelocity (v : Field) : Vec → CVec :=
  𝓕 (fun x : Vec => complexify (v x))

/-- The Leray symbol, equal to the identity at zero by the scalar zero
division convention. Its zero-frequency value is immaterial in L2. -/
def transverseSymbol (ξ : Vec) (z : CVec) : CVec :=
  z - ((∑ i : Fin 3, (ξ i : ℂ) * z i) / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) • complexify ξ

def complexCross (ξ : Vec) (z : CVec) : CVec :=
  WithLp.toLp 2 (crossProduct (fun i : Fin 3 => (ξ i : ℂ)) (fun i => z i))

def helicitySign (σ : Fin 2) : ℝ := if σ = 0 then 1 else -1

def helicalSymbol (σ : Fin 2) (ξ : Vec) (z : CVec) : CVec :=
  (1 / 2 : ℂ) • (transverseSymbol ξ z +
    (((helicitySign σ : ℝ) : ℂ) * Complex.I / (‖ξ‖ : ℂ)) • complexCross ξ z)

def helicalPower (σ : Fin 2) (v : Field) (ξ : Vec) : ℝ :=
  ‖helicalSymbol σ ξ (fourierVelocity v ξ)‖ ^ 2

/-- Actual inverse-Fourier physical Leray field. The later bridge proves
that on Schwartz inputs this is the smooth representative of the L2 Leray
projection; the definition itself does not assume that theorem. -/
def physicalLeray (v : Field) : Field :=
  fun x => realify (𝓕⁻ (fun ξ : Vec => transverseSymbol ξ (fourierVelocity v ξ)) x)

def CompactTemporalCorrection (a b : ℝ) (V : Velocity) : Prop :=
  ContDiff ℝ ∞ (fun z : ℝ × Vec => V z.1 z.2) ∧
  GlobalSchwartzBounds V ∧ HasCompactSupport V ∧ tsupport V ⊆ Ioo a b

/-- One compact temporal carrier works for all velocity and force corrections. -/
def CommonTemporalSupport (a b ε : ℝ) (u F : Velocity)
    (U G : ℝ → Velocity) : Prop :=
  ∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioo a b ∧
    ∀ lam : ℝ, |lam| < ε →
      tsupport (U lam - u) ⊆ K ∧ tsupport (G lam - F) ⊆ K

def ExactRealizationAndAgreement (ν T a b ε : ℝ)
    (u : Velocity) (p : Pressure) (F : Velocity)
    (U G : ℝ → Velocity) : Prop :=
  ∀ lam : ℝ, |lam| < ε →
    PreterminalNSE ν T (U lam) p (G lam) ∧
    LocalSchwartz T (U lam) ∧ AdmissibleForce (G lam) ∧
    U lam 0 = u 0 ∧
    CompactTemporalCorrection a b (U lam - u) ∧
    CompactTemporalCorrection a b (G lam - F) ∧
    (∀ t : ℝ, t ∉ Ioo a b → U lam t = u t ∧ G lam t = F t) ∧
    BoundedEnergy T (U lam) ∧ FiniteDissipation T (U lam) ∧
    CompactLocalBlowup T (U lam)

def CompleteHelicalPowerPreservation (T ε : ℝ) (u : Velocity)
    (U : ℝ → Velocity) : Prop :=
  (∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T,
    ∀ ξ : Vec, ξ ≠ 0 → ∀ σ : Fin 2,
      helicalPower σ (U lam t) ξ = helicalPower σ (u t) ξ) ∧
  ∃ ρ : ℝ, 0 < ρ ∧ ∀ lam : ℝ, |lam| < ε →
    ∀ t ∈ Ico (0 : ℝ) T, ∀ ξ : Vec, ‖ξ‖ < ρ →
      fourierVelocity (U lam t) ξ = fourierVelocity (u t) ξ

def TranslationSeparation (tstar ε : ℝ) (U : ℝ → Velocity) : Prop :=
  ∀ lam eta : ℝ, |lam| < ε → |eta| < ε → lam ≠ eta →
    ¬ ∃ y : Vec, ∀ x : Vec, U lam tstar x = U eta tstar (x + y)

def PhysicalProjectedForceSeparation (T ε : ℝ) (G : ℝ → Velocity) : Prop :=
  ∀ lam eta : ℝ, |lam| < ε → |eta| < ε → lam ≠ eta →
    ∃ t ∈ Ico (0 : ℝ) T, ∃ x : Vec, physicalLeray ((G lam - G eta) t) x ≠ 0

/-- Independent pointwise bounds for all jets avoid a totalized unbounded
supremum. This is equivalent, up to a finite factor, to the stated sum of
weighted C^r sup-seminorms. -/
def WeightedSmoothSmallness (ε : ℝ) (u F : Velocity)
    (U G : ℝ → Velocity) : Prop :=
  ∀ N r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, |lam| < ε →
    ∀ n : ℕ, n ≤ r → ∀ z : ℝ × Vec,
      weightedJet N n (U lam - u) z + weightedJet N n (G lam - F) z ≤ C * |lam|

def EnergyDissipationPreservation (T ε : ℝ) (u : Velocity)
    (U : ℝ → Velocity) : Prop :=
  ∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T,
    (∫ x : Vec, ‖U lam t x‖ ^ 2) = (∫ x : Vec, ‖u t x‖ ^ 2) ∧
      dissipation (U lam t) = dissipation (u t)

/-- The canonical whole-space target, with one common witness tuple. -/
def Family (ν T : ℝ) (u : Velocity) (p : Pressure) (F : Velocity) : Prop :=
  ∀ s ∈ Ico (0 : ℝ) T,
    ∃ a b tstar ε : ℝ, ∃ U G : ℝ → Velocity,
      s < a ∧ a < tstar ∧ tstar < b ∧ b < T ∧ ε = Real.pi / 4 ∧
      U 0 = u ∧ G 0 = F ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
        (U q.1 - u) q.2.1 q.2.2) {q | |q.1| < ε} ∧
      ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
        (G q.1 - F) q.2.1 q.2.2) {q | |q.1| < ε} ∧
      CommonTemporalSupport a b ε u F U G ∧
      ExactRealizationAndAgreement ν T a b ε u p F U G ∧
      CompleteHelicalPowerPreservation T ε u U ∧
      TranslationSeparation tstar ε U ∧
      PhysicalProjectedForceSeparation T ε G ∧
      WeightedSmoothSmallness ε u F U G ∧
      EnergyDissipationPreservation T ε u U

@[simp] theorem realify_complexify (v : Vec) : realify (complexify v) = v := by
  ext i
  rfl

theorem weightedJet_nonneg (N n : ℕ) (V : Velocity) (z : ℝ × Vec) :
    0 ≤ weightedJet N n V z := by
  unfold weightedJet
  positivity

theorem gradientSquare_nonneg (v : Field) (x : Vec) :
    0 ≤ gradientSquare v x :=
  Finset.sum_nonneg (fun _ _ => sq_nonneg _)

theorem Seed.initial_divergence_free {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) : ∀ x : Vec, divergence (u 0) x = 0 :=
  h.front.divergence_free 0 ⟨le_rfl, h.terminal_pos⟩

theorem compactLocalBlowup_of_late_eq {T r : ℝ} {u v : Velocity}
    (hr : r < T) (hu : CompactLocalBlowup T u)
    (heq : ∀ t ∈ Ioo r T, v t = u t) : CompactLocalBlowup T v := by
  obtain ⟨K, hK, hblow⟩ := hu
  refine ⟨K, hK, ?_⟩
  intro s hs M hM
  have hm : max s r ∈ Ico (0 : ℝ) T :=
    ⟨le_trans hs.1 (le_max_left s r), max_lt_iff.mpr ⟨hs.2, hr⟩⟩
  obtain ⟨t, ht, x, hx, hlarge⟩ := hblow (max s r) hm M hM
  refine ⟨t, ⟨lt_of_le_of_lt (le_max_left s r) ht.1, ht.2⟩, x, hx, ?_⟩
  rw [heq t ⟨lt_of_le_of_lt (le_max_right s r) ht.1, ht.2⟩]
  exact hlarge

theorem CompactLocalBlowup.exists_nonzero_after {T : ℝ} {u : Velocity}
    (h : CompactLocalBlowup T u) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) :
    ∃ t ∈ Ioo s T, ∃ x : Vec, u t x ≠ 0 := by
  obtain ⟨K, _, hblow⟩ := h
  obtain ⟨t, ht, x, _, hx⟩ := hblow s hs 0 le_rfl
  exact ⟨t, ht, x, norm_pos_iff.mp hx⟩

end

end MethbokeAddon.FDSNR3
