import MethbokeAddon.WeakFouriermanB.LocalClassicalUniqueness

/-!
# One maximal physical classical trajectory from actual local existence

The lifetime is the extended nonnegative supremum of the durations of all
actual positive initial classical fronts. At each covered time one front is
chosen. Physical velocity and normalized-pressure uniqueness prove that these
choices agree with every supplied front; the resulting single pair therefore
has every shorter finite-front restriction.

The construction is conditional on an actual initial front, or on the explicit
local-existence premise in the final existence wrapper. It does not prove that
premise, an H1-controlled lifespan, or the full WFB conclusion. No existence,
uniqueness or continuation assertion is introduced as an axiom.

Prepared source only; external cached compilation and fresh exact-type/axiom
audits are required. No local Lean, Lake or kernel execution was used.
-/

set_option autoImplicit false

open Set SingularClosure
open scoped ENNReal

namespace MethbokeAddon.WeakFouriermanB
noncomputable section

/-- A single physical pair on every positive finite interval below its
extended lifetime. Every other admitted initial front agrees with this pair,
and its duration is bounded by the lifetime. The last field excludes any
proper classical extension, including one given by a different representative.
-/
structure MaximalClassicalFront (ν : ℝ) (a : Field)
    (u : Velocity) (p : Pressure) (Tmax : ℝ≥0∞) : Prop where
  lifetime_pos : 0 < Tmax
  initial : u 0 = a
  finite_front : ∀ T : ℝ, 0 < T → ENNReal.ofReal T < Tmax →
    InitialClassicalFront ν T a u p
  agreement : ∀ (T : ℝ) (v : Velocity) (q : Pressure), 0 < T →
    InitialClassicalFront ν T a v q →
    ∀ r ∈ Ico (0 : ℝ) T, u r = v r ∧ p r = q r
  no_extension : ∀ (T : ℝ) (v : Velocity) (q : Pressure), 0 < T →
    InitialClassicalFront ν T a v q → ENNReal.ofReal T ≤ Tmax

private structure MaximalFrontWitness (ν : ℝ) (a : Field) where
  horizon : ℝ
  horizon_pos : 0 < horizon
  velocity : Velocity
  pressure : Pressure
  front : InitialClassicalFront ν horizon a velocity pressure

private def canonicalClassicalLifetime (ν : ℝ) (a : Field) : ℝ≥0∞ :=
  ⨆ F : MaximalFrontWitness ν a, ENNReal.ofReal F.horizon

private def canonicalClassicalVelocity (ν : ℝ) (a : Field) : Velocity := by
  classical
  exact fun t => if h : ∃ F : MaximalFrontWitness ν a, t < F.horizon then
    (Classical.choose h).velocity t else 0

private def canonicalClassicalPressure (ν : ℝ) (a : Field) : Pressure := by
  classical
  exact fun t => if h : ∃ F : MaximalFrontWitness ν a, t < F.horizon then
    (Classical.choose h).pressure t else 0

private theorem canonicalClassicalPair_agrees
    (ν : ℝ) (a : Field) (hν : 0 < ν) (F : MaximalFrontWitness ν a)
    (t : ℝ) (ht : t ∈ Ico (0 : ℝ) F.horizon) :
    canonicalClassicalVelocity ν a t = F.velocity t ∧
      canonicalClassicalPressure ν a t = F.pressure t := by
  classical
  have hex : ∃ G : MaximalFrontWitness ν a, t < G.horizon := ⟨F, ht.2⟩
  let G : MaximalFrontWitness ν a := Classical.choose hex
  have hGt : t < G.horizon := Classical.choose_spec hex
  have hagree := initial_classical_front_unique ν G.horizon F.horizon a
    G.velocity F.velocity G.pressure F.pressure hν G.horizon_pos F.horizon_pos
    G.front F.front t ⟨ht.1, lt_min hGt ht.2⟩
  simpa only [canonicalClassicalVelocity, canonicalClassicalPressure,
    dif_pos hex, G] using hagree

/-- Construct an actual maximal pair from one actual positive initial front.
There is no norm-controlled local-existence assertion in this theorem.
-/
theorem maximal_classical_front_exists_of_front
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (H : InitialClassicalFront ν T a u p) :
    ∃ Tmax : ℝ≥0∞, ∃ (U : Velocity) (P : Pressure),
      MaximalClassicalFront ν a U P Tmax := by
  let F : MaximalFrontWitness ν a := ⟨T, hT, u, p, H⟩
  have hFle : ENNReal.ofReal F.horizon ≤ canonicalClassicalLifetime ν a :=
    le_iSup (fun G : MaximalFrontWitness ν a => ENNReal.ofReal G.horizon) F
  refine ⟨canonicalClassicalLifetime ν a, canonicalClassicalVelocity ν a,
    canonicalClassicalPressure ν a, ?_⟩
  refine {
    lifetime_pos := (ENNReal.ofReal_pos.mpr F.horizon_pos).trans_le hFle
    initial := (canonicalClassicalPair_agrees ν a hν F 0
      ⟨le_rfl, F.horizon_pos⟩).1.trans F.front.initial
    finite_front := ?_
    agreement := ?_
    no_extension := ?_
  }
  · intro S hS hSlife
    change ENNReal.ofReal S <
      ⨆ G : MaximalFrontWitness ν a, ENNReal.ofReal G.horizon at hSlife
    obtain ⟨G, hSG⟩ := lt_iSup_iff.mp hSlife
    have hSGreal : S < G.horizon :=
      (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hS.le).mp hSG
    have HG := initial_front_restrict ν G.horizon S a G.velocity G.pressure
      G.front hSGreal.le
    apply initial_front_congr ν S a G.velocity (canonicalClassicalVelocity ν a)
      G.pressure (canonicalClassicalPressure ν a) HG hS
    · intro r hr
      exact (canonicalClassicalPair_agrees ν a hν G r
        ⟨hr.1, hr.2.trans hSGreal⟩).1
    · intro r hr
      exact (canonicalClassicalPair_agrees ν a hν G r
        ⟨hr.1, hr.2.trans hSGreal⟩).2
  · intro S v q hS K r hr
    exact canonicalClassicalPair_agrees ν a hν ⟨S, hS, v, q, K⟩ r hr
  · intro S v q hS K
    exact le_iSup (fun G : MaximalFrontWitness ν a => ENNReal.ofReal G.horizon)
      ⟨S, hS, v, q, K⟩

/-- Explicit local existence is the only construction premise beyond smooth
data and positive viscosity. It must be discharged by the physical local
theory before this theorem can close the maximal-trajectory WFB obligation.
-/
theorem maximal_classical_front_exists_of_local_existence
    (ν : ℝ) (hν : 0 < ν)
    (hLocal : ∀ b : Field, SmoothSigmaZero b →
      ∃ T : ℝ, 0 < T ∧ ∃ (v : Velocity) (q : Pressure),
        InitialClassicalFront ν T b v q)
    (a : Field) (ha : SmoothSigmaZero a) :
    ∃ Tmax : ℝ≥0∞, ∃ (U : Velocity) (P : Pressure),
      MaximalClassicalFront ν a U P Tmax := by
  obtain ⟨T, hT, u, p, H⟩ := hLocal a ha
  exact maximal_classical_front_exists_of_front ν T a u p hν hT H

/-- The no-extension and finite-restriction properties determine a unique
extended lifetime, including the infinite-lifetime case.
-/
theorem maximal_classical_front_lifetime_unique
    (ν : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (Tmax Smax : ℝ≥0∞)
    (H : MaximalClassicalFront ν a u p Tmax)
    (K : MaximalClassicalFront ν a v q Smax) : Tmax = Smax := by
  apply le_antisymm
  · by_contra h
    have hST : Smax < Tmax := lt_of_not_ge h
    obtain ⟨T, _, hSTreal, hTTmax⟩ := ENNReal.lt_iff_exists_real_btwn.mp hST
    have hT : 0 < T := ENNReal.ofReal_pos.mp (K.lifetime_pos.trans hSTreal)
    exact (not_le_of_gt hSTreal)
      (K.no_extension T u p hT (H.finite_front T hT hTTmax))
  · by_contra h
    have hTS : Tmax < Smax := lt_of_not_ge h
    obtain ⟨T, _, hTTreal, hTSmax⟩ := ENNReal.lt_iff_exists_real_btwn.mp hTS
    have hT : 0 < T := ENNReal.ofReal_pos.mp (H.lifetime_pos.trans hTTreal)
    exact (not_le_of_gt hTTreal)
      (H.no_extension T v q hT (K.finite_front T hT hTSmax))

/-- Both the lifetime and the actual velocity/normalized-pressure path are
unique on the physical interval. Values at or beyond a finite lifetime are
unconstrained and are not asserted equal.
-/
theorem maximal_classical_front_unique
    (ν : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (Tmax Smax : ℝ≥0∞)
    (H : MaximalClassicalFront ν a u p Tmax)
    (K : MaximalClassicalFront ν a v q Smax) :
    Tmax = Smax ∧ ∀ r : ℝ, 0 ≤ r → ENNReal.ofReal r < Tmax →
      u r = v r ∧ p r = q r := by
  have hmax := maximal_classical_front_lifetime_unique ν a u v p q Tmax Smax H K
  refine ⟨hmax, ?_⟩
  intro r hr0 hrmax
  obtain ⟨T, _, hrT, hTmax⟩ := ENNReal.lt_iff_exists_real_btwn.mp hrmax
  have hrTreal : r < T := (ENNReal.ofReal_lt_ofReal_iff_of_nonneg hr0).mp hrT
  have hT : 0 < T := hr0.trans_lt hrTreal
  have hTSmax : ENNReal.ofReal T < Smax := hTmax.trans_le hmax.le
  exact H.agreement T v q hT (K.finite_front T hT hTSmax) r ⟨hr0, hrTreal⟩

end
end MethbokeAddon.WeakFouriermanB
