import FDSNContracts.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set MeasureTheory
open scoped BigOperators ContDiff
open SingularClosure MethbokeAddon.FDSN

noncomputable section

/- Exact consumer types and literal physical definitions. -/
example : ℝ → Set (ℝ × Vec) := preterminalSpacetime
example (T : ℝ) : preterminalSpacetime T = {z : ℝ × Vec | z.1 ∈ Ico (0 : ℝ) T} := rfl
example : ℝ → ℝ → Velocity → Pressure → Velocity → Prop := PreterminalNSE
example : ℝ → Velocity → Prop := BoundedCellEnergy
example (T : ℝ) (u : Velocity) : BoundedCellEnergy T u ↔
    ∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Ico (0 : ℝ) T,
      IntegrableOn (fun x => ‖u t x‖ ^ 2) unitCube volume ∧
        (∫ x in unitCube, ‖u t x‖ ^ 2) ≤ E := Iff.rfl
example : Field → Vec → ℝ := gradientSquare
example (v : Field) (x : Vec) :
    gradientSquare v x = ∑ i : Fin 3, ‖coordinateDerivative v i x‖ ^ 2 := rfl
example : Field → ℝ := cellDissipation
example (v : Field) : cellDissipation v = ∫ x in unitCube, gradientSquare v x := rfl
example : ℝ → Velocity → Prop := FiniteDissipation
example (T : ℝ) (u : Velocity) : FiniteDissipation T u ↔
    (∀ t ∈ Ico (0 : ℝ) T, IntegrableOn (gradientSquare (u t)) unitCube volume) ∧
      IntegrableOn (fun t => cellDissipation (u t)) (Ioo (0 : ℝ) T) volume := Iff.rfl
example : ℝ → Velocity → Prop := CofinalVelocityBlowup
example (T : ℝ) (u : Velocity) : CofinalVelocityBlowup T u ↔
    ∀ s ∈ Ico (0 : ℝ) T, ∀ M : ℝ, 0 ≤ M →
      ∃ t ∈ Ioo s T, ∃ x ∈ unitCube, M < ‖u t x‖ := Iff.rfl
example : ℝ → ℝ → Velocity → Pressure → Velocity → Prop := Seed

/- Explicit projections audit the actual hypotheses of the Seed. -/
example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F) : 0 < ν :=
  h.viscosity_pos
example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F) : 0 < T :=
  h.terminal_pos
example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F) :
    PreterminalNSE ν T u p F := h.front
example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F) :
    MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce F := h.force
example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F) :
    ContDiff ℝ ∞ (u 0) := h.initial_smooth
example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F) :
    BoundedCellEnergy T u := h.bounded_energy
example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F) :
    FiniteDissipation T u := h.finite_dissipation
example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F) :
    CofinalVelocityBlowup T u := h.terminal_blowup
example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F) :
    SpatialPeriodic (u 0) := h.initial_periodic
example {ν T : ℝ} {u F : Velocity} {p : Pressure} (h : Seed ν T u p F) :
    ∀ x : Vec, divergence (u 0) x = 0 := h.initial_divergence_free

example (v : Field) (x : Vec) : 0 ≤ gradientSquare v x := gradientSquare_nonneg v x
example {T r : ℝ} {u v : Velocity} (hr : r < T) (hu : CofinalVelocityBlowup T u)
    (heq : ∀ t ∈ Ioo r T, v t = u t) : CofinalVelocityBlowup T v :=
  cofinalVelocityBlowup_of_late_eq hr hu heq
example {F G : Velocity}
    (hF : MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce F)
    (hG : MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce G) :
    MethbokeAddon.FeffermanFamily.AdmissiblePeriodicForce (F + G) :=
  admissiblePeriodicForce_add hF hG

#print PreterminalNSE
#print Seed

end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.preterminalSpacetime"
#check @MethbokeAddon.FDSN.preterminalSpacetime
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.preterminalSpacetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.preterminalSpacetime"
#print axioms MethbokeAddon.FDSN.preterminalSpacetime
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.preterminalSpacetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PreterminalNSE"
#check @MethbokeAddon.FDSN.PreterminalNSE
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PreterminalNSE"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PreterminalNSE"
#print axioms MethbokeAddon.FDSN.PreterminalNSE
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PreterminalNSE"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.BoundedCellEnergy"
#check @MethbokeAddon.FDSN.BoundedCellEnergy
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.BoundedCellEnergy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.BoundedCellEnergy"
#print axioms MethbokeAddon.FDSN.BoundedCellEnergy
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.BoundedCellEnergy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.gradientSquare"
#check @MethbokeAddon.FDSN.gradientSquare
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.gradientSquare"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.gradientSquare"
#print axioms MethbokeAddon.FDSN.gradientSquare
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.gradientSquare"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.cellDissipation"
#check @MethbokeAddon.FDSN.cellDissipation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.cellDissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.cellDissipation"
#print axioms MethbokeAddon.FDSN.cellDissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.cellDissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.FiniteDissipation"
#check @MethbokeAddon.FDSN.FiniteDissipation
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.FiniteDissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.FiniteDissipation"
#print axioms MethbokeAddon.FDSN.FiniteDissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.FiniteDissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.CofinalVelocityBlowup"
#check @MethbokeAddon.FDSN.CofinalVelocityBlowup
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.CofinalVelocityBlowup"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.CofinalVelocityBlowup"
#print axioms MethbokeAddon.FDSN.CofinalVelocityBlowup
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.CofinalVelocityBlowup"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed"
#check @MethbokeAddon.FDSN.Seed
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed"
#print axioms MethbokeAddon.FDSN.Seed
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed.initial_periodic"
#check @MethbokeAddon.FDSN.Seed.initial_periodic
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed.initial_periodic"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed.initial_periodic"
#print axioms MethbokeAddon.FDSN.Seed.initial_periodic
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed.initial_periodic"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.Seed.initial_divergence_free"
#check @MethbokeAddon.FDSN.Seed.initial_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.Seed.initial_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.Seed.initial_divergence_free"
#print axioms MethbokeAddon.FDSN.Seed.initial_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.Seed.initial_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.gradientSquare_nonneg"
#check @MethbokeAddon.FDSN.gradientSquare_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.gradientSquare_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.gradientSquare_nonneg"
#print axioms MethbokeAddon.FDSN.gradientSquare_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.gradientSquare_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.cofinalVelocityBlowup_of_late_eq"
#check @MethbokeAddon.FDSN.cofinalVelocityBlowup_of_late_eq
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.cofinalVelocityBlowup_of_late_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.cofinalVelocityBlowup_of_late_eq"
#print axioms MethbokeAddon.FDSN.cofinalVelocityBlowup_of_late_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.cofinalVelocityBlowup_of_late_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.admissiblePeriodicForce_add"
#check @MethbokeAddon.FDSN.admissiblePeriodicForce_add
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.admissiblePeriodicForce_add"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.admissiblePeriodicForce_add"
#print axioms MethbokeAddon.FDSN.admissiblePeriodicForce_add
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.admissiblePeriodicForce_add"

