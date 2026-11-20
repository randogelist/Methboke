import FDSNR3Contracts.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ContDiff FourierTransform

/- Independent literal consumers fix the whole-space contract rather than
merely checking that a named predicate can be mentioned. -/

example : CVec = EuclideanSpace ℂ (Fin 3) := rfl

example (v : Vec) :
    complexify v = WithLp.toLp 2 (fun i : Fin 3 => (v i : ℂ)) := rfl

example (v : CVec) :
    realify v = WithLp.toLp 2 (fun i : Fin 3 => (v i).re) := rfl

example (T : ℝ) :
    preterminalSpacetime T = {z : ℝ × Vec | z.1 ∈ Ico (0 : ℝ) T} := rfl

example (N n : ℕ) (V : Velocity) (z : ℝ × Vec) :
    weightedJet N n V z =
      (1 + ‖z.2‖) ^ N *
        ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => V y.1 y.2) z‖ := rfl

example (T : ℝ) (N n : ℕ) (V : Velocity) (z : ℝ × Vec) :
    weightedJetWithin T N n V z =
      (1 + ‖z.2‖) ^ N *
        ‖iteratedFDerivWithin ℝ n (fun y : ℝ × Vec => V y.1 y.2)
          (preterminalSpacetime T) z‖ := rfl

example (V : Velocity) :
    GlobalSchwartzBounds V =
      (∀ N n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × Vec, weightedJet N n V z ≤ C) := rfl

example (T : ℝ) (V : Velocity) :
    LocalSchwartz T V =
      (ContDiffOn ℝ ∞ (fun z : ℝ × Vec => V z.1 z.2) (preterminalSpacetime T) ∧
        ∀ b ∈ Ico (0 : ℝ) T, ∀ N n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
          ∀ t ∈ Icc (0 : ℝ) b, ∀ x : Vec, weightedJetWithin T N n V (t, x) ≤ C) := rfl

example (F : Velocity) :
    AdmissibleForce F ↔
      ContDiff ℝ ∞ (fun z : ℝ × Vec => F z.1 z.2) ∧
      GlobalSchwartzBounds F ∧
      ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ t : ℝ, t ∉ Icc a b → F t = 0 :=
  ⟨fun h => ⟨h.smooth, h.schwartz_bounds, h.time_support⟩,
    fun h => ⟨h.1, h.2.1, h.2.2⟩⟩

example (ν T : ℝ) (u : Velocity) (p : Pressure) (F : Velocity) :
    PreterminalNSE ν T u p F ↔
      ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (preterminalSpacetime T) ∧
      ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2) (preterminalSpacetime T) ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (u t) x = 0) ∧
      (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
        timeDerivative u t x + convection (u t) x + SingularClosure.gradient (p t) x =
          ν • laplacian (u t) x + F t x) :=
  ⟨fun h => ⟨h.velocity_smooth, h.pressure_smooth, h.divergence_free, h.equation⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2⟩⟩

example (T : ℝ) (u : Velocity) :
    BoundedEnergy T u =
      (∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Ico (0 : ℝ) T,
        Integrable (fun x : Vec => ‖u t x‖ ^ 2) volume ∧
          (∫ x : Vec, ‖u t x‖ ^ 2) ≤ E) := rfl

example (v : Field) (x : Vec) :
    gradientSquare v x = ∑ i : Fin 3, ‖coordinateDerivative v i x‖ ^ 2 := rfl

example (v : Field) :
    dissipation v = ∫ x : Vec, gradientSquare v x := rfl

example (T : ℝ) (u : Velocity) :
    FiniteDissipation T u =
      ((∀ t ∈ Ico (0 : ℝ) T, Integrable (gradientSquare (u t)) volume) ∧
        IntegrableOn (fun t => dissipation (u t)) (Ioo (0 : ℝ) T) volume) := rfl

example (T : ℝ) (u : Velocity) :
    CompactLocalBlowup T u =
      (∃ K : Set Vec, IsCompact K ∧
        ∀ s ∈ Ico (0 : ℝ) T, ∀ M : ℝ, 0 ≤ M →
          ∃ t ∈ Ioo s T, ∃ x ∈ K, M < ‖u t x‖) := rfl

example (ν T : ℝ) (u : Velocity) (p : Pressure) (F : Velocity) :
    Seed ν T u p F ↔
      0 < ν ∧ 0 < T ∧ PreterminalNSE ν T u p F ∧
      LocalSchwartz T u ∧ AdmissibleForce F ∧
      BoundedEnergy T u ∧ FiniteDissipation T u ∧ CompactLocalBlowup T u :=
  ⟨fun h => ⟨h.viscosity_pos, h.terminal_pos, h.front, h.local_schwartz,
      h.force, h.bounded_energy, h.finite_dissipation, h.terminal_blowup⟩,
    fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1,
      h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2⟩⟩

example (v : Field) :
    fourierVelocity v = 𝓕 (fun x : Vec => complexify (v x)) := rfl

example (ξ : Vec) (z : CVec) :
    transverseSymbol ξ z =
      z - ((∑ i : Fin 3, (ξ i : ℂ) * z i) / ((‖ξ‖ ^ 2 : ℝ) : ℂ)) •
        complexify ξ := rfl

example (ξ : Vec) (z : CVec) :
    complexCross ξ z =
      WithLp.toLp 2 (crossProduct (fun i : Fin 3 => (ξ i : ℂ)) (fun i => z i)) := rfl

example (σ : Fin 2) :
    helicitySign σ = (if σ = 0 then (1 : ℝ) else -1) := rfl

example (σ : Fin 2) (ξ : Vec) (z : CVec) :
    helicalSymbol σ ξ z =
      (1 / 2 : ℂ) • (transverseSymbol ξ z +
        (((helicitySign σ : ℝ) : ℂ) * Complex.I / (‖ξ‖ : ℂ)) • complexCross ξ z) := rfl

example (σ : Fin 2) (v : Field) (ξ : Vec) :
    helicalPower σ v ξ = ‖helicalSymbol σ ξ (fourierVelocity v ξ)‖ ^ 2 := rfl

example (v : Field) :
    physicalLeray v =
      (fun x => realify
        (𝓕⁻ (fun ξ : Vec => transverseSymbol ξ (fourierVelocity v ξ)) x)) := rfl

example (a b : ℝ) (V : Velocity) :
    CompactTemporalCorrection a b V =
      (ContDiff ℝ ∞ (fun z : ℝ × Vec => V z.1 z.2) ∧
        GlobalSchwartzBounds V ∧ HasCompactSupport V ∧ tsupport V ⊆ Ioo a b) := rfl

example (a b ε : ℝ) (u F : Velocity) (U G : ℝ → Velocity) :
    CommonTemporalSupport a b ε u F U G =
      (∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioo a b ∧
        ∀ lam : ℝ, |lam| < ε →
          tsupport (U lam - u) ⊆ K ∧ tsupport (G lam - F) ⊆ K) := rfl

example (ν T a b ε : ℝ) (u : Velocity) (p : Pressure) (F : Velocity)
    (U G : ℝ → Velocity) :
    ExactRealizationAndAgreement ν T a b ε u p F U G =
      (∀ lam : ℝ, |lam| < ε →
        PreterminalNSE ν T (U lam) p (G lam) ∧
        LocalSchwartz T (U lam) ∧ AdmissibleForce (G lam) ∧
        U lam 0 = u 0 ∧
        CompactTemporalCorrection a b (U lam - u) ∧
        CompactTemporalCorrection a b (G lam - F) ∧
        (∀ t : ℝ, t ∉ Ioo a b → U lam t = u t ∧ G lam t = F t) ∧
        BoundedEnergy T (U lam) ∧ FiniteDissipation T (U lam) ∧
        CompactLocalBlowup T (U lam)) := rfl

example (T ε : ℝ) (u : Velocity) (U : ℝ → Velocity) :
    CompleteHelicalPowerPreservation T ε u U =
      ((∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T,
          ∀ ξ : Vec, ξ ≠ 0 → ∀ σ : Fin 2,
            helicalPower σ (U lam t) ξ = helicalPower σ (u t) ξ) ∧
        ∃ ρ : ℝ, 0 < ρ ∧ ∀ lam : ℝ, |lam| < ε →
          ∀ t ∈ Ico (0 : ℝ) T, ∀ ξ : Vec, ‖ξ‖ < ρ →
            fourierVelocity (U lam t) ξ = fourierVelocity (u t) ξ) := rfl

example (tstar ε : ℝ) (U : ℝ → Velocity) :
    TranslationSeparation tstar ε U =
      (∀ lam eta : ℝ, |lam| < ε → |eta| < ε → lam ≠ eta →
        ¬ ∃ y : Vec, ∀ x : Vec, U lam tstar x = U eta tstar (x + y)) := rfl

example (T ε : ℝ) (G : ℝ → Velocity) :
    PhysicalProjectedForceSeparation T ε G =
      (∀ lam eta : ℝ, |lam| < ε → |eta| < ε → lam ≠ eta →
        ∃ t ∈ Ico (0 : ℝ) T, ∃ x : Vec,
          physicalLeray ((G lam - G eta) t) x ≠ 0) := rfl

example (ε : ℝ) (u F : Velocity) (U G : ℝ → Velocity) :
    WeightedSmoothSmallness ε u F U G =
      (∀ N r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, |lam| < ε →
        ∀ n : ℕ, n ≤ r → ∀ z : ℝ × Vec,
          weightedJet N n (U lam - u) z + weightedJet N n (G lam - F) z ≤ C * |lam|) := rfl

example (T ε : ℝ) (u : Velocity) (U : ℝ → Velocity) :
    EnergyDissipationPreservation T ε u U =
      (∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T,
        (∫ x : Vec, ‖U lam t x‖ ^ 2) = (∫ x : Vec, ‖u t x‖ ^ 2) ∧
          dissipation (U lam t) = dissipation (u t)) := rfl

example (ν T : ℝ) (u : Velocity) (p : Pressure) (F : Velocity) :
    Family ν T u p F =
      (∀ s ∈ Ico (0 : ℝ) T,
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
          EnergyDissipationPreservation T ε u U) := rfl

/- Complete theorem consumers: no inferred proxy theorem types. -/

example (v : Vec) : realify (complexify v) = v :=
  realify_complexify v

example (N n : ℕ) (V : Velocity) (z : ℝ × Vec) :
    0 ≤ weightedJet N n V z :=
  weightedJet_nonneg N n V z

example (v : Field) (x : Vec) : 0 ≤ gradientSquare v x :=
  gradientSquare_nonneg v x

example {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (h : Seed ν T u p F) : ∀ x : Vec, divergence (u 0) x = 0 :=
  Seed.initial_divergence_free h

example {T r : ℝ} {u v : Velocity}
    (hr : r < T) (hu : CompactLocalBlowup T u)
    (heq : ∀ t ∈ Ioo r T, v t = u t) : CompactLocalBlowup T v :=
  compactLocalBlowup_of_late_eq hr hu heq

example {T : ℝ} {u : Velocity}
    (h : CompactLocalBlowup T u) {s : ℝ} (hs : s ∈ Ico (0 : ℝ) T) :
    ∃ t ∈ Ioo s T, ∃ x : Vec, u t x ≠ 0 :=
  CompactLocalBlowup.exists_nonzero_after h hs

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.CVec"
#check @MethbokeAddon.FDSNR3.CVec
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.CVec"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.CVec"
#print axioms MethbokeAddon.FDSNR3.CVec
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.CVec"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexify"
#check @MethbokeAddon.FDSNR3.complexify
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexify"
#print axioms MethbokeAddon.FDSNR3.complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.realify"
#check @MethbokeAddon.FDSNR3.realify
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.realify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.realify"
#print axioms MethbokeAddon.FDSNR3.realify
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.realify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.preterminalSpacetime"
#check @MethbokeAddon.FDSNR3.preterminalSpacetime
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.preterminalSpacetime"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.preterminalSpacetime"
#print axioms MethbokeAddon.FDSNR3.preterminalSpacetime
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.preterminalSpacetime"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.weightedJet"
#check @MethbokeAddon.FDSNR3.weightedJet
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.weightedJet"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.weightedJet"
#print axioms MethbokeAddon.FDSNR3.weightedJet
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.weightedJet"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.weightedJetWithin"
#check @MethbokeAddon.FDSNR3.weightedJetWithin
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.weightedJetWithin"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.weightedJetWithin"
#print axioms MethbokeAddon.FDSNR3.weightedJetWithin
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.weightedJetWithin"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.GlobalSchwartzBounds"
#check @MethbokeAddon.FDSNR3.GlobalSchwartzBounds
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.GlobalSchwartzBounds"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.GlobalSchwartzBounds"
#print axioms MethbokeAddon.FDSNR3.GlobalSchwartzBounds
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.GlobalSchwartzBounds"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz"
#check @MethbokeAddon.FDSNR3.LocalSchwartz
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.LocalSchwartz"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.LocalSchwartz"
#print axioms MethbokeAddon.FDSNR3.LocalSchwartz
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.LocalSchwartz"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.AdmissibleForce"
#check @MethbokeAddon.FDSNR3.AdmissibleForce
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.AdmissibleForce"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.AdmissibleForce"
#print axioms MethbokeAddon.FDSNR3.AdmissibleForce
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.AdmissibleForce"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.PreterminalNSE"
#check @MethbokeAddon.FDSNR3.PreterminalNSE
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.PreterminalNSE"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.PreterminalNSE"
#print axioms MethbokeAddon.FDSNR3.PreterminalNSE
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.PreterminalNSE"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.BoundedEnergy"
#check @MethbokeAddon.FDSNR3.BoundedEnergy
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.BoundedEnergy"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.BoundedEnergy"
#print axioms MethbokeAddon.FDSNR3.BoundedEnergy
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.BoundedEnergy"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.gradientSquare"
#check @MethbokeAddon.FDSNR3.gradientSquare
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.gradientSquare"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.gradientSquare"
#print axioms MethbokeAddon.FDSNR3.gradientSquare
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.gradientSquare"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.dissipation"
#check @MethbokeAddon.FDSNR3.dissipation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.dissipation"
#print axioms MethbokeAddon.FDSNR3.dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.dissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.FiniteDissipation"
#check @MethbokeAddon.FDSNR3.FiniteDissipation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.FiniteDissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.FiniteDissipation"
#print axioms MethbokeAddon.FDSNR3.FiniteDissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.FiniteDissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.CompactLocalBlowup"
#check @MethbokeAddon.FDSNR3.CompactLocalBlowup
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.CompactLocalBlowup"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.CompactLocalBlowup"
#print axioms MethbokeAddon.FDSNR3.CompactLocalBlowup
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.CompactLocalBlowup"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.Seed"
#check @MethbokeAddon.FDSNR3.Seed
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.Seed"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.Seed"
#print axioms MethbokeAddon.FDSNR3.Seed
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.Seed"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity"
#check @MethbokeAddon.FDSNR3.fourierVelocity
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.fourierVelocity"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.fourierVelocity"
#print axioms MethbokeAddon.FDSNR3.fourierVelocity
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.fourierVelocity"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol"
#check @MethbokeAddon.FDSNR3.transverseSymbol
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.transverseSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.transverseSymbol"
#print axioms MethbokeAddon.FDSNR3.transverseSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.transverseSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.complexCross"
#check @MethbokeAddon.FDSNR3.complexCross
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.complexCross"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.complexCross"
#print axioms MethbokeAddon.FDSNR3.complexCross
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.complexCross"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicitySign"
#check @MethbokeAddon.FDSNR3.helicitySign
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicitySign"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicitySign"
#print axioms MethbokeAddon.FDSNR3.helicitySign
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicitySign"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol"
#check @MethbokeAddon.FDSNR3.helicalSymbol
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalSymbol"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalSymbol"
#print axioms MethbokeAddon.FDSNR3.helicalSymbol
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalSymbol"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.helicalPower"
#check @MethbokeAddon.FDSNR3.helicalPower
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.helicalPower"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.helicalPower"
#print axioms MethbokeAddon.FDSNR3.helicalPower
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.helicalPower"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.physicalLeray"
#check @MethbokeAddon.FDSNR3.physicalLeray
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.physicalLeray"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.physicalLeray"
#print axioms MethbokeAddon.FDSNR3.physicalLeray
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.physicalLeray"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.CompactTemporalCorrection"
#check @MethbokeAddon.FDSNR3.CompactTemporalCorrection
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.CompactTemporalCorrection"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.CompactTemporalCorrection"
#print axioms MethbokeAddon.FDSNR3.CompactTemporalCorrection
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.CompactTemporalCorrection"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.CommonTemporalSupport"
#check @MethbokeAddon.FDSNR3.CommonTemporalSupport
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.CommonTemporalSupport"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.CommonTemporalSupport"
#print axioms MethbokeAddon.FDSNR3.CommonTemporalSupport
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.CommonTemporalSupport"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.ExactRealizationAndAgreement"
#check @MethbokeAddon.FDSNR3.ExactRealizationAndAgreement
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.ExactRealizationAndAgreement"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.ExactRealizationAndAgreement"
#print axioms MethbokeAddon.FDSNR3.ExactRealizationAndAgreement
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.ExactRealizationAndAgreement"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.CompleteHelicalPowerPreservation"
#check @MethbokeAddon.FDSNR3.CompleteHelicalPowerPreservation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.CompleteHelicalPowerPreservation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.CompleteHelicalPowerPreservation"
#print axioms MethbokeAddon.FDSNR3.CompleteHelicalPowerPreservation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.CompleteHelicalPowerPreservation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.TranslationSeparation"
#check @MethbokeAddon.FDSNR3.TranslationSeparation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.TranslationSeparation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.TranslationSeparation"
#print axioms MethbokeAddon.FDSNR3.TranslationSeparation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.TranslationSeparation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.PhysicalProjectedForceSeparation"
#check @MethbokeAddon.FDSNR3.PhysicalProjectedForceSeparation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.PhysicalProjectedForceSeparation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.PhysicalProjectedForceSeparation"
#print axioms MethbokeAddon.FDSNR3.PhysicalProjectedForceSeparation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.PhysicalProjectedForceSeparation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.WeightedSmoothSmallness"
#check @MethbokeAddon.FDSNR3.WeightedSmoothSmallness
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.WeightedSmoothSmallness"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.WeightedSmoothSmallness"
#print axioms MethbokeAddon.FDSNR3.WeightedSmoothSmallness
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.WeightedSmoothSmallness"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.EnergyDissipationPreservation"
#check @MethbokeAddon.FDSNR3.EnergyDissipationPreservation
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.EnergyDissipationPreservation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.EnergyDissipationPreservation"
#print axioms MethbokeAddon.FDSNR3.EnergyDissipationPreservation
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.EnergyDissipationPreservation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.Family"
#check @MethbokeAddon.FDSNR3.Family
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.Family"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.Family"
#print axioms MethbokeAddon.FDSNR3.Family
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.Family"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.realify_complexify"
#check @MethbokeAddon.FDSNR3.realify_complexify
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.realify_complexify"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.realify_complexify"
#print axioms MethbokeAddon.FDSNR3.realify_complexify
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.realify_complexify"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.weightedJet_nonneg"
#check @MethbokeAddon.FDSNR3.weightedJet_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.weightedJet_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.weightedJet_nonneg"
#print axioms MethbokeAddon.FDSNR3.weightedJet_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.weightedJet_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.gradientSquare_nonneg"
#check @MethbokeAddon.FDSNR3.gradientSquare_nonneg
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.gradientSquare_nonneg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.gradientSquare_nonneg"
#print axioms MethbokeAddon.FDSNR3.gradientSquare_nonneg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.gradientSquare_nonneg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.Seed.initial_divergence_free"
#check @MethbokeAddon.FDSNR3.Seed.initial_divergence_free
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.Seed.initial_divergence_free"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.Seed.initial_divergence_free"
#print axioms MethbokeAddon.FDSNR3.Seed.initial_divergence_free
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.Seed.initial_divergence_free"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.compactLocalBlowup_of_late_eq"
#check @MethbokeAddon.FDSNR3.compactLocalBlowup_of_late_eq
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.compactLocalBlowup_of_late_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.compactLocalBlowup_of_late_eq"
#print axioms MethbokeAddon.FDSNR3.compactLocalBlowup_of_late_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.compactLocalBlowup_of_late_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.CompactLocalBlowup.exists_nonzero_after"
#check @MethbokeAddon.FDSNR3.CompactLocalBlowup.exists_nonzero_after
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.CompactLocalBlowup.exists_nonzero_after"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.CompactLocalBlowup.exists_nonzero_after"
#print axioms MethbokeAddon.FDSNR3.CompactLocalBlowup.exists_nonzero_after
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.CompactLocalBlowup.exists_nonzero_after"

