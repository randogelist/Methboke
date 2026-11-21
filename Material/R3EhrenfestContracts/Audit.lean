import R3EhrenfestContracts.Endpoint

set_option pp.universes true
set_option pp.explicit true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open MeasureTheory Set
open scoped BigOperators ContDiff

namespace R3EhrenfestContracts.ExpectedTypes

open MethbokeAddon.QuasiFeffermanA
open MethbokeAddon.R3Ehrenfest

-- Full Euclidean space, unrestricted pressure, and genuine Schwartz data.
example : Space = EuclideanSpace ℝ (Fin 3) := rfl
example (a : SmoothDatum) : SchwartzMap (EuclideanSpace ℝ (Fin 3))
    (EuclideanSpace ℝ (Fin 3)) := a.value
example (a : SchwartzMap Space Space)
    (ha : ∀ x : Space, SingularClosure.divergence a x = 0) : SmoothDatum := ⟨a, ha⟩
example (a : SmoothDatum) : ∀ x : Space, SingularClosure.divergence a.value x = 0 :=
  a.divergence_free

-- Integrability is retained alongside one uniform bound for every time.
example (u : SingularClosure.Velocity) :
    UniformFiniteEnergy u ↔
      ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, 0 ≤ t →
        Integrable (fun x : Space => ‖u t x‖ ^ 2) volume ∧
          (∫ x : Space, ‖u t x‖ ^ 2) ≤ E := Iff.rfl

-- A literal solution is constructible from exactly these physical clauses.
-- There is no pressure gauge, Sobolev premise, projected equation or stopped bound.
example (ν : ℝ) (a : SmoothDatum) (u : SingularClosure.Velocity)
    (p : SingularClosure.Pressure)
    (hu : ContDiffOn ℝ ∞ (fun z : ℝ × Space => u z.1 z.2) {z | 0 ≤ z.1})
    (hp : ContDiffOn ℝ ∞ (fun z : ℝ × Space => p z.1 z.2) {z | 0 ≤ z.1})
    (hdiv : ∀ t : ℝ, 0 ≤ t → ∀ x : Space, SingularClosure.divergence (u t) x = 0)
    (heq : ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      SingularClosure.timeDerivative u t x + SingularClosure.convection (u t) x +
        SingularClosure.gradient (p t) x = ν • SingularClosure.laplacian (u t) x)
    (hinit : u 0 = a.value)
    (henergy : ∃ E : ℝ, 0 ≤ E ∧ ∀ t : ℝ, 0 ≤ t →
      Integrable (fun x : Space => ‖u t x‖ ^ 2) volume ∧
        (∫ x : Space, ‖u t x‖ ^ 2) ≤ E) : GlobalSmoothNSE ν a u p :=
  ⟨hu, hp, hdiv, heq, hinit, henergy⟩

example (ν : ℝ) (a : SmoothDatum) (u : SingularClosure.Velocity)
    (p : SingularClosure.Pressure) (h : GlobalSmoothNSE ν a u p) :
    u 0 = a.value := h.initial
example (ν : ℝ) (a : SmoothDatum) (u : SingularClosure.Velocity)
    (p : SingularClosure.Pressure) (h : GlobalSmoothNSE ν a u p) :
    ∀ t : ℝ, 0 ≤ t → ∀ x : Space,
      derivWithin (fun s : ℝ => u s x) (Ici (0 : ℝ)) t +
        fderiv ℝ (u t) x (u t x) +
        SingularClosure.gradient (p t) x = ν • SingularClosure.laplacian (u t) x :=
  h.equation
example (ν : ℝ) :
    NSE_A ν ↔ ∀ a : SmoothDatum,
      ∃ (u : SingularClosure.Velocity) (p : SingularClosure.Pressure),
        GlobalSmoothNSE ν a u p := Iff.rfl

-- Elementary consistency, not nonzero-data existence or an obstruction witness.
example : SmoothDatum := zeroDatum
example : zeroDatum.value = (0 : SchwartzMap Space Space) := rfl
example : UniformFiniteEnergy (0 : SingularClosure.Velocity) := uniformFiniteEnergy_zero
example (ν : ℝ) : GlobalSmoothNSE ν zeroDatum
    (0 : SingularClosure.Velocity) (0 : SingularClosure.Pressure) := globalSmoothNSE_zero ν

-- The counterexample premise remains explicit and is not constructed here.
example {ν : ℝ} (a : SmoothDatum)
    (ha : ∀ (u : SingularClosure.Velocity) (p : SingularClosure.Pressure),
      ¬ GlobalSmoothNSE ν a u p) : ¬ NSE_A ν := not_NSE_A_of_counterexample a ha

end R3EhrenfestContracts.ExpectedTypes

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothDatum"
#check @MethbokeAddon.R3Ehrenfest.SmoothDatum
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.SmoothDatum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.SmoothDatum"
#print axioms MethbokeAddon.R3Ehrenfest.SmoothDatum
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.SmoothDatum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.UniformFiniteEnergy"
#check @MethbokeAddon.R3Ehrenfest.UniformFiniteEnergy
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.UniformFiniteEnergy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.UniformFiniteEnergy"
#print axioms MethbokeAddon.R3Ehrenfest.UniformFiniteEnergy
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.UniformFiniteEnergy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.GlobalSmoothNSE"
#check @MethbokeAddon.R3Ehrenfest.GlobalSmoothNSE
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.GlobalSmoothNSE"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.GlobalSmoothNSE"
#print axioms MethbokeAddon.R3Ehrenfest.GlobalSmoothNSE
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.GlobalSmoothNSE"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.NSE_A"
#check @MethbokeAddon.R3Ehrenfest.NSE_A
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.NSE_A"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.NSE_A"
#print axioms MethbokeAddon.R3Ehrenfest.NSE_A
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.NSE_A"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.zeroDatum"
#check @MethbokeAddon.R3Ehrenfest.zeroDatum
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.zeroDatum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.zeroDatum"
#print axioms MethbokeAddon.R3Ehrenfest.zeroDatum
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.zeroDatum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.uniformFiniteEnergy_zero"
#check @MethbokeAddon.R3Ehrenfest.uniformFiniteEnergy_zero
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.uniformFiniteEnergy_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.uniformFiniteEnergy_zero"
#print axioms MethbokeAddon.R3Ehrenfest.uniformFiniteEnergy_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.uniformFiniteEnergy_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.globalSmoothNSE_zero"
#check @MethbokeAddon.R3Ehrenfest.globalSmoothNSE_zero
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.globalSmoothNSE_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.globalSmoothNSE_zero"
#print axioms MethbokeAddon.R3Ehrenfest.globalSmoothNSE_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.globalSmoothNSE_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.R3Ehrenfest.not_NSE_A_of_counterexample"
#check @MethbokeAddon.R3Ehrenfest.not_NSE_A_of_counterexample
#eval IO.println "TYPE_END:MethbokeAddon.R3Ehrenfest.not_NSE_A_of_counterexample"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.R3Ehrenfest.not_NSE_A_of_counterexample"
#print axioms MethbokeAddon.R3Ehrenfest.not_NSE_A_of_counterexample
#eval IO.println "AXIOMS_END:MethbokeAddon.R3Ehrenfest.not_NSE_A_of_counterexample"
