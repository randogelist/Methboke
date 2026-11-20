import FDSNR3Main.Endpoint

set_option pp.universes true
set_option pp.fullNames true

set_option autoImplicit false

open Set Filter MeasureTheory SingularClosure MethbokeAddon.FDSNR3
open scoped BigOperators ContDiff FourierTransform SchwartzMap Topology

noncomputable section

example {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (hseed : Seed ν T u p F) : Family ν T u p F :=
  MethbokeAddon.FDSNR3.FDSN_R3 hseed

/- The independent literal consumer expands every logical Family predicate,
including the fields of PreterminalNSE and AdmissibleForce. Weighted jets
are the actual iterated Frechet derivatives. Native operators and the
original Seed premise retain their separately audited definitions. -/
example {ν T : ℝ} {u F : Velocity} {p : Pressure}
    (hseed : Seed ν T u p F) :
    ∀ s ∈ Ico (0 : ℝ) T,
      ∃ a b tstar ε : ℝ, ∃ U G : ℝ → Velocity,
        s < a ∧ a < tstar ∧ tstar < b ∧ b < T ∧ ε = Real.pi / 4 ∧
        U 0 = u ∧ G 0 = F ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
          (U q.1 - u) q.2.1 q.2.2) {q | |q.1| < ε} ∧
        ContDiffOn ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
          (G q.1 - F) q.2.1 q.2.2) {q | |q.1| < ε} ∧
        (∃ K : Set ℝ, IsCompact K ∧ K ⊆ Ioo a b ∧
          ∀ lam : ℝ, |lam| < ε →
            tsupport (U lam - u) ⊆ K ∧ tsupport (G lam - F) ⊆ K) ∧
        (∀ lam : ℝ, |lam| < ε →
          (ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U lam z.1 z.2)
              {z | z.1 ∈ Ico (0 : ℝ) T} ∧
            ContDiffOn ℝ ∞ (fun z : ℝ × Vec => p z.1 z.2)
              {z | z.1 ∈ Ico (0 : ℝ) T} ∧
            (∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec, divergence (U lam t) x = 0) ∧
            ∀ t ∈ Ico (0 : ℝ) T, ∀ x : Vec,
              timeDerivative (U lam) t x + convection (U lam t) x +
                  SingularClosure.gradient (p t) x =
                ν • laplacian (U lam t) x + G lam t x) ∧
          (ContDiffOn ℝ ∞ (fun z : ℝ × Vec => U lam z.1 z.2)
              {z | z.1 ∈ Ico (0 : ℝ) T} ∧
            ∀ c ∈ Ico (0 : ℝ) T, ∀ N n : ℕ, ∃ C : ℝ, 0 ≤ C ∧
              ∀ t ∈ Icc (0 : ℝ) c, ∀ x : Vec,
                (1 + ‖x‖) ^ N *
                  ‖iteratedFDerivWithin ℝ n (fun z : ℝ × Vec => U lam z.1 z.2)
                    {z | z.1 ∈ Ico (0 : ℝ) T} (t, x)‖ ≤ C) ∧
          (ContDiff ℝ ∞ (fun z : ℝ × Vec => G lam z.1 z.2) ∧
            (∀ N n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × Vec,
              (1 + ‖z.2‖) ^ N *
                ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => G lam y.1 y.2) z‖ ≤ C) ∧
            ∃ c d : ℝ, 0 < c ∧ c < d ∧
              ∀ t : ℝ, t ∉ Icc c d → G lam t = 0) ∧
          U lam 0 = u 0 ∧
          (ContDiff ℝ ∞ (fun z : ℝ × Vec => (U lam - u) z.1 z.2) ∧
            (∀ N n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × Vec,
              (1 + ‖z.2‖) ^ N *
                ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => (U lam - u) y.1 y.2) z‖ ≤ C) ∧
            HasCompactSupport (U lam - u) ∧ tsupport (U lam - u) ⊆ Ioo a b) ∧
          (ContDiff ℝ ∞ (fun z : ℝ × Vec => (G lam - F) z.1 z.2) ∧
            (∀ N n : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ × Vec,
              (1 + ‖z.2‖) ^ N *
                ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => (G lam - F) y.1 y.2) z‖ ≤ C) ∧
            HasCompactSupport (G lam - F) ∧ tsupport (G lam - F) ⊆ Ioo a b) ∧
          (∀ t : ℝ, t ∉ Ioo a b → U lam t = u t ∧ G lam t = F t) ∧
          (∃ E : ℝ, 0 ≤ E ∧ ∀ t ∈ Ico (0 : ℝ) T,
            Integrable (fun x : Vec => ‖U lam t x‖ ^ 2) volume ∧
              (∫ x : Vec, ‖U lam t x‖ ^ 2) ≤ E) ∧
          ((∀ t ∈ Ico (0 : ℝ) T, Integrable (gradientSquare (U lam t)) volume) ∧
            IntegrableOn (fun t => dissipation (U lam t)) (Ioo (0 : ℝ) T) volume) ∧
          ∃ K : Set Vec, IsCompact K ∧
            ∀ r ∈ Ico (0 : ℝ) T, ∀ M : ℝ, 0 ≤ M →
              ∃ t ∈ Ioo r T, ∃ x ∈ K, M < ‖U lam t x‖) ∧
        ((∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T,
          ∀ ξ : Vec, ξ ≠ 0 → ∀ σ : Fin 2,
            helicalPower σ (U lam t) ξ = helicalPower σ (u t) ξ) ∧
          ∃ ρ : ℝ, 0 < ρ ∧ ∀ lam : ℝ, |lam| < ε →
            ∀ t ∈ Ico (0 : ℝ) T, ∀ ξ : Vec, ‖ξ‖ < ρ →
              fourierVelocity (U lam t) ξ = fourierVelocity (u t) ξ) ∧
        (∀ lam eta : ℝ, |lam| < ε → |eta| < ε → lam ≠ eta →
          ¬ ∃ y : Vec, ∀ x : Vec, U lam tstar x = U eta tstar (x + y)) ∧
        (∀ lam eta : ℝ, |lam| < ε → |eta| < ε → lam ≠ eta →
          ∃ t ∈ Ico (0 : ℝ) T, ∃ x : Vec,
            physicalLeray ((G lam - G eta) t) x ≠ 0) ∧
        (∀ N r : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ lam : ℝ, |lam| < ε →
          ∀ n : ℕ, n ≤ r → ∀ z : ℝ × Vec,
            (1 + ‖z.2‖) ^ N *
                ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => (U lam - u) y.1 y.2) z‖ +
              (1 + ‖z.2‖) ^ N *
                ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => (G lam - F) y.1 y.2) z‖ ≤
              C * |lam|) ∧
        (∀ lam : ℝ, |lam| < ε → ∀ t ∈ Ico (0 : ℝ) T,
          (∫ x : Vec, ‖U lam t x‖ ^ 2) = (∫ x : Vec, ‖u t x‖ ^ 2) ∧
            dissipation (U lam t) = dissipation (u t)) := by
  intro s hs
  obtain ⟨a, b, tstar, ε, U, G, hsa, hat, htb, hbT, hε, hU0, hG0,
      hUsmooth, hGsmooth, hcommon, hrealization, hpowers, htranslation,
      hforceSeparation, hsmall, hhistory⟩ := MethbokeAddon.FDSNR3.FDSN_R3 hseed s hs
  refine ⟨a, b, tstar, ε, U, G, hsa, hat, htb, hbT, hε, hU0, hG0,
    hUsmooth, hGsmooth, hcommon, ?_, hpowers, htranslation, hforceSeparation,
    hsmall, hhistory⟩
  intro lam hlam
  obtain ⟨hfront, hlocal, hforce, hinitial, hvelocityCorrection, hforceCorrection,
    houtside, hboundedEnergy, hfiniteDissipation, hblowup⟩ := hrealization lam hlam
  exact ⟨⟨hfront.velocity_smooth, hfront.pressure_smooth,
      hfront.divergence_free, hfront.equation⟩,
    hlocal, ⟨hforce.smooth, hforce.schwartz_bounds, hforce.time_support⟩,
    hinitial, hvelocityCorrection, hforceCorrection, houtside,
    hboundedEnergy, hfiniteDissipation, hblowup⟩

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.FDSN_R3"
#check @MethbokeAddon.FDSNR3.FDSN_R3
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.FDSN_R3"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.FDSN_R3"
#print axioms MethbokeAddon.FDSNR3.FDSN_R3
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.FDSN_R3"

