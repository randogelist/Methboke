import QFAZeroDatum.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped BigOperators ContDiff Interval Topology

namespace QFAZeroDatum.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.QuasiFeffermanA.PhysicalRoot
open MethbokeAddon.QuasiFeffermanA.ZeroDatum
open QFA.Representation

-- Literal whole-space carriers: neither periodicity nor mean-zero is present.
example : MethbokeAddon.QuasiFeffermanA.Space = EuclideanSpace ℝ (Fin 3) := rfl
example : SpatialL2 = Lp (EuclideanSpace ℝ (Fin 3)) 2
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) := rfl
example : EnergyDatum = {a : SpatialL2 // Solenoidal a} := rfl

-- The root is a definition with the frozen exact numerical cutoff.
example (ν : ℝ) (a : SpatialL2) :
    cutoff ν a = 8 * ‖a‖ ^ 4 / (27 * Real.pi ^ 4 * ν ^ 5) := rfl
example (δ : ℝ) : tailSpacetime δ =
    {z : ℝ × MethbokeAddon.QuasiFeffermanA.Space | δ ≤ z.1} := rfl
example : ℝ → ℝ → SingularClosure.Velocity → SingularClosure.Pressure → Prop :=
  ClassicalTail
example (ν δ : ℝ) (v : SingularClosure.Velocity) (p : SingularClosure.Pressure)
    (h : ClassicalTail ν δ v p) :
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℝ × MethbokeAddon.QuasiFeffermanA.Space => v z.1 z.2)
        {z | δ ≤ z.1} ∧
    ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
        (fun z : ℝ × MethbokeAddon.QuasiFeffermanA.Space => p z.1 z.2)
        {z | δ ≤ z.1} ∧
    (∀ t : ℝ, δ ≤ t → ∀ x : MethbokeAddon.QuasiFeffermanA.Space,
      SingularClosure.divergence (v t) x = 0) ∧
    (∀ t : ℝ, δ ≤ t → ∀ x : MethbokeAddon.QuasiFeffermanA.Space,
      SingularClosure.timeDerivative v t x + SingularClosure.convection (v t) x +
        SingularClosure.gradient (p t) x = ν • SingularClosure.laplacian (v t) x) ∧
    (∀ t : ℝ, δ ≤ t → p t 0 = 0) :=
  ⟨h.velocity_smooth, h.pressure_smooth, h.divergence_free, h.equation, h.pressure_normalized⟩
example (ν δ : ℝ) (v : SingularClosure.Velocity) (p : SingularClosure.Pressure)
    (hv : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × MethbokeAddon.QuasiFeffermanA.Space => v z.1 z.2) {z | δ ≤ z.1})
    (hp : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : ℝ × MethbokeAddon.QuasiFeffermanA.Space => p z.1 z.2) {z | δ ≤ z.1})
    (hd : ∀ t : ℝ, δ ≤ t → ∀ x : MethbokeAddon.QuasiFeffermanA.Space,
      SingularClosure.divergence (v t) x = 0)
    (he : ∀ t : ℝ, δ ≤ t → ∀ x : MethbokeAddon.QuasiFeffermanA.Space,
      SingularClosure.timeDerivative v t x + SingularClosure.convection (v t) x +
        SingularClosure.gradient (p t) x = ν • SingularClosure.laplacian (v t) x)
    (hg : ∀ t : ℝ, δ ≤ t → p t 0 = 0) : ClassicalTail ν δ v p :=
  ⟨hv, hp, hd, he, hg⟩
example (ν δ : ℝ) (u : Velocity) :
    HasSmoothTail ν u δ =
      (∃ (v : SingularClosure.Velocity) (p : SingularClosure.Pressure),
        ClassicalTail ν δ v p ∧ ∀ t : ℝ, δ ≤ t →
          (u t : MethbokeAddon.QuasiFeffermanA.Space → MethbokeAddon.QuasiFeffermanA.Space)
            =ᵐ[volume] v t) := rfl
example (ν δ : ℝ) (u : Velocity) (G : WeakGradient) :
    TailEnergyEquality ν u G δ =
      (∀ t : ℝ, δ ≤ t →
        ‖u t‖ ^ 2 + 2 * ν * (∫ r in δ..t, ∑ j : Fin 3, ‖G r j‖ ^ 2) = ‖u δ‖ ^ 2) := rfl
example (u v : Velocity) : SameVelocity u v = (∀ t : ℝ, 0 ≤ t → u t = v t) := rfl
example (ν δ : ℝ) (u : Velocity) (G : WeakGradient) :
    UniqueFuture ν u G δ =
      (LerayHopf ν (u δ) (fun t => u (δ + t)) (fun t => G (δ + t)) ∧
        ∀ (v : Velocity) (H : WeakGradient), LerayHopf ν (u δ) v H →
          ∀ t : ℝ, 0 ≤ t → u (δ + t) = v t) := rfl
example (ν : ℝ) (a : SpatialL2) :
    DatumConclusion ν a =
      ((∃ (u : Velocity) (G : WeakGradient), LerayHopf ν a u G) ∧
        ∀ (u : Velocity) (G : WeakGradient), LerayHopf ν a u G →
          ∀ δ : ℝ, 8 * ‖a‖ ^ 4 / (27 * Real.pi ^ 4 * ν ^ 5) < δ →
            HasSmoothTail ν u δ ∧ TailEnergyEquality ν u G δ ∧ UniqueFuture ν u G δ) := rfl
example (ν : ℝ) (a : SpatialL2) :
    ClosedDatumConclusion ν a =
      ((∃ (u : Velocity) (G : WeakGradient), LerayHopf ν a u G) ∧
        ∀ (u : Velocity) (G : WeakGradient), LerayHopf ν a u G →
          ∀ δ : ℝ, 8 * ‖a‖ ^ 4 / (27 * Real.pi ^ 4 * ν ^ 5) ≤ δ →
            HasSmoothTail ν u δ ∧ TailEnergyEquality ν u G δ ∧ UniqueFuture ν u G δ) := rfl
example : MethbokeAddon.QuasiFeffermanA.PhysicalRoot.QuasiFeffermanA =
    (∀ ν : ℝ, 0 < ν → ∀ a : EnergyDatum, DatumConclusion ν a.val) := rfl
example : ClosedQuasiFeffermanA =
    (∀ ν : ℝ, 0 < ν → ∀ a : EnergyDatum, ClosedDatumConclusion ν a.val) := rfl
example {ν : ℝ} {a : SpatialL2} (h : ClosedDatumConclusion ν a) : DatumConclusion ν a :=
  ClosedDatumConclusion.strict h

-- Zero objects are literal zero L2 classes, not selected pointwise representatives.
example : zeroVelocity = (fun _ : ℝ => (0 : SpatialL2)) := rfl
example : zeroGradient = (fun (_ : ℝ) (_ : Fin 3) => (0 : SpatialL2)) := rfl
example : Solenoidal (0 : SpatialL2) := zero_solenoidal
example : SpatialWeakGradient (0 : SpatialL2) (fun _ : Fin 3 => 0) := zero_spatialWeakGradient
example (ν : ℝ) : WeakMomentum ν zeroVelocity zeroGradient := zero_weakMomentum ν
example (ν : ℝ) : WeakMomentum ν (fun _ => 0) (fun _ _ => 0) := zero_weakMomentum ν
example (ν : ℝ) : LerayHopf ν 0 zeroVelocity zeroGradient := zero_lerayHopf ν
example (ν : ℝ) : LerayHopf ν (0 : SpatialL2) (fun _ => 0) (fun _ _ => 0) := zero_lerayHopf ν
example (ν δ : ℝ) :
    ClassicalTail ν δ (0 : SingularClosure.Velocity) (0 : SingularClosure.Pressure) :=
  zero_classicalTail ν δ
example (ν : ℝ) : cutoff ν (0 : SpatialL2) = 0 := cutoff_zero ν

-- Conclusions retain every supplied zero-datum weak path and its gradient witness.
example {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 ≤ ν) {t : ℝ} (ht : 0 ≤ t) : u t = 0 :=
  zeroDatum_velocity_eq_zero h hν ht
example {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) {t : ℝ} (ht : 0 ≤ t) :
    (∫ r in (0 : ℝ)..t, gradientEnergy (G r)) = 0 :=
  zeroDatum_initial_dissipation_eq_zero h hν ht
example {ν δ t : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) (hδ : 0 ≤ δ) (ht : δ ≤ t) :
    (∫ r in δ..t, ∑ j : Fin 3, ‖G r j‖ ^ 2) = 0 :=
  zeroDatum_tail_dissipation_eq_zero h hν hδ ht
example {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) {δ : ℝ} (hδ : 0 ≤ δ) :
    TailEnergyEquality ν u G δ := zeroDatum_tailEnergyEquality h hν hδ
example {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) {δ : ℝ} (hδ : 0 ≤ δ) :
    EnergyStart ν u G δ := zeroDatum_energyStart h hν hδ
example {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 ≤ ν) {δ : ℝ} (hδ : 0 ≤ δ) :
    HasSmoothTail ν u δ := zeroDatum_hasSmoothTail h hν hδ
example {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) {δ : ℝ} (hδ : 0 ≤ δ) :
    UniqueFuture ν u G δ := zeroDatum_uniqueFuture h hν hδ
example {ν : ℝ} {u : Velocity} {G : WeakGradient}
    (h : LerayHopf ν 0 u G) (hν : 0 < ν) {δ : ℝ} (hδ : 0 ≤ δ) :
    LerayHopf ν (u δ) (fun t => u (δ + t)) (fun t => G (δ + t)) ∧
      ∀ (v : Velocity) (H : WeakGradient), LerayHopf ν (u δ) v H →
        ∀ t : ℝ, 0 ≤ t → u (δ + t) = v t := zeroDatum_uniqueFuture h hν hδ

-- Both exact roots and a separately expanded closed-cutoff consumer.
example (ν : ℝ) (hν : 0 < ν) : ClosedDatumConclusion ν (0 : SpatialL2) :=
  closedDatumConclusion_zero ν hν
example (ν : ℝ) (hν : 0 < ν) : DatumConclusion ν (0 : SpatialL2) :=
  datumConclusion_zero ν hν
example (ν : ℝ) (hν : 0 < ν) :
    (∃ (u : Velocity) (G : WeakGradient), LerayHopf ν (0 : SpatialL2) u G) ∧
      ∀ (u : Velocity) (G : WeakGradient), LerayHopf ν (0 : SpatialL2) u G →
        ∀ δ : ℝ, 0 ≤ δ →
          (∃ (v : SingularClosure.Velocity) (p : SingularClosure.Pressure),
            ClassicalTail ν δ v p ∧ ∀ t : ℝ, δ ≤ t →
              (u t : MethbokeAddon.QuasiFeffermanA.Space → MethbokeAddon.QuasiFeffermanA.Space)
                =ᵐ[volume] v t) ∧
          (∀ t : ℝ, δ ≤ t →
            ‖u t‖ ^ 2 + 2 * ν * (∫ r in δ..t, ∑ j : Fin 3, ‖G r j‖ ^ 2) = ‖u δ‖ ^ 2) ∧
          (LerayHopf ν (u δ) (fun t => u (δ + t)) (fun t => G (δ + t)) ∧
            ∀ (v : Velocity) (H : WeakGradient), LerayHopf ν (u δ) v H →
              ∀ t : ℝ, 0 ≤ t → u (δ + t) = v t) := by
  have h := closedDatumConclusion_zero ν hν
  exact ⟨h.1, fun u G hu δ hδ => h.2 u G hu δ (by simpa only [cutoff_zero] using hδ)⟩

end QFAZeroDatum.ExpectedTypes

-- Ordered named type and axiom evidence follows.

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.cutoff"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.cutoff
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.cutoff"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.cutoff"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.cutoff
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.cutoff"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.tailSpacetime"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.tailSpacetime
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.tailSpacetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.tailSpacetime"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.tailSpacetime
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.tailSpacetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClassicalTail"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClassicalTail
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClassicalTail"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClassicalTail"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClassicalTail
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClassicalTail"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.HasSmoothTail"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.HasSmoothTail
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.HasSmoothTail"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.HasSmoothTail"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.HasSmoothTail
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.HasSmoothTail"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.TailEnergyEquality"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.TailEnergyEquality
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.TailEnergyEquality"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.TailEnergyEquality"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.TailEnergyEquality
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.TailEnergyEquality"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.SameVelocity"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.SameVelocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.SameVelocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.SameVelocity"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.SameVelocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.SameVelocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.UniqueFuture"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.UniqueFuture
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.UniqueFuture"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.UniqueFuture"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.UniqueFuture
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.UniqueFuture"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.DatumConclusion"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.DatumConclusion
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.DatumConclusion"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.DatumConclusion"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.DatumConclusion
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.DatumConclusion"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.QuasiFeffermanA"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.QuasiFeffermanA
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.QuasiFeffermanA"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.QuasiFeffermanA"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.QuasiFeffermanA
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.QuasiFeffermanA"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedQuasiFeffermanA"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedQuasiFeffermanA
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedQuasiFeffermanA"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedQuasiFeffermanA"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedQuasiFeffermanA
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedQuasiFeffermanA"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion.strict"
#check @MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion.strict
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion.strict"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion.strict"
#print axioms MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion.strict
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.PhysicalRoot.ClosedDatumConclusion.strict"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroVelocity"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroVelocity
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroVelocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroVelocity"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroVelocity
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroVelocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroGradient"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_solenoidal"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_solenoidal"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_spatialWeakGradient"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_spatialWeakGradient
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_spatialWeakGradient"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_spatialWeakGradient"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_spatialWeakGradient
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_spatialWeakGradient"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_weakMomentum"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_weakMomentum
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_weakMomentum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_weakMomentum"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_weakMomentum
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_weakMomentum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_lerayHopf"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_lerayHopf
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_lerayHopf"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_lerayHopf"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_lerayHopf
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_lerayHopf"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_classicalTail"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_classicalTail
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_classicalTail"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_classicalTail"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_classicalTail
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zero_classicalTail"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.cutoff_zero"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.cutoff_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.cutoff_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.cutoff_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.cutoff_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.cutoff_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_velocity_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_velocity_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_velocity_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_velocity_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_velocity_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_velocity_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_initial_dissipation_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_initial_dissipation_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_initial_dissipation_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_initial_dissipation_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_initial_dissipation_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_initial_dissipation_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tail_dissipation_eq_zero"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tail_dissipation_eq_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tail_dissipation_eq_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tail_dissipation_eq_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tail_dissipation_eq_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tail_dissipation_eq_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tailEnergyEquality"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tailEnergyEquality
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tailEnergyEquality"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tailEnergyEquality"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tailEnergyEquality
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_tailEnergyEquality"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_energyStart"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_energyStart
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_energyStart"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_energyStart"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_energyStart
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_energyStart"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_hasSmoothTail"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_hasSmoothTail
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_hasSmoothTail"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_hasSmoothTail"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_hasSmoothTail
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_hasSmoothTail"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_uniqueFuture"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_uniqueFuture
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_uniqueFuture"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_uniqueFuture"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_uniqueFuture
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.zeroDatum_uniqueFuture"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.closedDatumConclusion_zero"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.closedDatumConclusion_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.closedDatumConclusion_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.closedDatumConclusion_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.closedDatumConclusion_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.closedDatumConclusion_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.datumConclusion_zero"
#check @MethbokeAddon.QuasiFeffermanA.ZeroDatum.datumConclusion_zero
#eval IO.println "TYPE_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.datumConclusion_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.QuasiFeffermanA.ZeroDatum.datumConclusion_zero"
#print axioms MethbokeAddon.QuasiFeffermanA.ZeroDatum.datumConclusion_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.QuasiFeffermanA.ZeroDatum.datumConclusion_zero"
