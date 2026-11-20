import FDSNR3Phase.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

noncomputable section

open Set
open scoped ComplexConjugate ContDiff Topology
open MethbokeAddon.FDSNR3

example {X : Type*} :
    (packetPhase : (ℝ → ℝ) → (X → ℝ) → ℝ → ℝ → X → ℂ) =
      (fun β ψ lam t ξ =>
        MethbokeAddon.FDSN.phase (lam * β t * ψ ξ)) := rfl

example {X : Type*} :
    (packetPhaseIncrement : (ℝ → ℝ) → (X → ℝ) → ℝ → ℝ → X → ℂ) =
      (fun β ψ lam t ξ => packetPhase β ψ lam t ξ - 1) := rfl

example {X V : Type*} [SMul ℂ V] :
    (packetRotate : (ℝ → ℝ) → (X → ℝ) → ℝ → ℝ → (X → V) → X → V) =
      (fun β ψ lam t c ξ => packetPhase β ψ lam t ξ • c ξ) := rfl

example {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ)
    (lam t : ℝ) (ξ : X) :
    packetPhase β ψ lam t ξ =
      Complex.exp (((lam * β t * ψ ξ : ℝ) : ℂ) * Complex.I) :=
  packetPhase_eq_exp β ψ lam t ξ

example {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ) (t : ℝ) (ξ : X) :
    packetPhase β ψ 0 t ξ = 1 := packetPhase_zero_parameter β ψ t ξ

example {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (ξ : X) :
    packetPhase β ψ lam t ξ ≠ 0 := packetPhase_ne_zero β ψ lam t ξ

example {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (ξ : X) :
    ‖packetPhase β ψ lam t ξ‖ = 1 := norm_packetPhase β ψ lam t ξ

example {X : Type*} [Neg X] (β : ℝ → ℝ) {ψ : X → ℝ}
    (hψ : ∀ ξ : X, ψ (-ξ) = -ψ ξ) (lam t : ℝ) (ξ : X) :
    packetPhase β ψ lam t (-ξ) = conj (packetPhase β ψ lam t ξ) :=
  packetPhase_neg β hψ lam t ξ

example {X : Type*} {β : ℝ → ℝ} (ψ : X → ℝ) (lam : ℝ) {t : ℝ}
    (hβ : β t = 0) (ξ : X) :
    packetPhase β ψ lam t ξ = 1 :=
  packetPhase_eq_one_of_beta_zero ψ lam hβ ξ

example {X : Type*} (β : ℝ → ℝ) {ψ : X → ℝ} (lam t : ℝ) {ξ : X}
    (hψ : ψ ξ = 0) :
    packetPhase β ψ lam t ξ = 1 :=
  packetPhase_eq_one_of_psi_zero β lam t hψ

example {X : Type*} {β : ℝ → ℝ} {ψ : X → ℝ} (lam : ℝ)
    {t : ℝ} {ξ : X} (hβ : β t = 1) (hψ : ψ ξ = 1) :
    packetPhase β ψ lam t ξ = MethbokeAddon.FDSN.phase lam :=
  packetPhase_at_normalization lam hβ hψ

example {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ) (t : ℝ) (ξ : X) :
    packetPhaseIncrement β ψ 0 t ξ = 0 :=
  packetPhaseIncrement_zero_parameter β ψ t ξ

example {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (ξ : X) :
    ‖packetPhaseIncrement β ψ lam t ξ‖ ≤ ‖lam‖ * ‖β t‖ * ‖ψ ξ‖ :=
  norm_packetPhaseIncrement_le β ψ lam t ξ

example {X : Type*} [TopologicalSpace X] (β : ℝ → ℝ) (ψ : X → ℝ)
    (lam t : ℝ) :
    tsupport (packetPhaseIncrement β ψ lam t) ⊆ tsupport ψ :=
  tsupport_packetPhaseIncrement_frequency_subset β ψ lam t

example {X : Type*} [TopologicalSpace X] (β : ℝ → ℝ) {ψ : X → ℝ}
    (hψ : HasCompactSupport ψ) (lam t : ℝ) :
    HasCompactSupport (packetPhaseIncrement β ψ lam t) :=
  hasCompactSupport_packetPhaseIncrement_frequency β hψ lam t

example {X : Type*} (β : ℝ → ℝ) (ψ : X → ℝ) (lam : ℝ) (ξ : X) :
    tsupport (fun t : ℝ => packetPhaseIncrement β ψ lam t ξ) ⊆ tsupport β :=
  tsupport_packetPhaseIncrement_time_subset β ψ lam ξ

example {X : Type*} {β : ℝ → ℝ} (hβ : HasCompactSupport β)
    (ψ : X → ℝ) (lam : ℝ) (ξ : X) :
    HasCompactSupport (fun t : ℝ => packetPhaseIncrement β ψ lam t ξ) :=
  hasCompactSupport_packetPhaseIncrement_time hβ ψ lam ξ

example {X V : Type*} [AddCommGroup V] [Module ℂ V]
    (β : ℝ → ℝ) (ψ : X → ℝ) (t : ℝ) (c : X → V) :
    packetRotate β ψ 0 t c = c := packetRotate_zero_parameter β ψ t c

example {X V : Type*} [AddCommGroup V] [Module ℂ V]
    {β : ℝ → ℝ} (ψ : X → ℝ) (lam : ℝ) {t : ℝ}
    (hβ : β t = 0) (c : X → V) :
    packetRotate β ψ lam t c = c :=
  packetRotate_eq_of_beta_zero ψ lam hβ c

example {X V : Type*} [AddCommGroup V] [Module ℂ V]
    (β : ℝ → ℝ) {ψ : X → ℝ} (lam t : ℝ) {ξ : X}
    (hψ : ψ ξ = 0) (c : X → V) :
    packetRotate β ψ lam t c ξ = c ξ :=
  packetRotate_eq_of_psi_zero β lam t hψ c

example {X V : Type*} [AddCommGroup V] [Module ℂ V]
    {β : ℝ → ℝ} {ψ : X → ℝ} (lam : ℝ) {t : ℝ} {ξ : X}
    (hβ : β t = 1) (hψ : ψ ξ = 1) (c : X → V) :
    packetRotate β ψ lam t c ξ = MethbokeAddon.FDSN.phase lam • c ξ :=
  packetRotate_at_normalization lam hβ hψ c

example {X V : Type*} [AddCommGroup V] [Module ℂ V]
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (c : X → V) (ξ : X) :
    packetRotate β ψ lam t c ξ - c ξ =
      packetPhaseIncrement β ψ lam t ξ • c ξ :=
  packetRotate_sub β ψ lam t c ξ

example {X V W : Type*} [AddCommGroup V] [Module ℂ V]
    [AddCommGroup W] [Module ℂ W]
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ)
    (c : X → V) (L : X → V →ₗ[ℂ] W)
    (hc : ∀ ξ : X, L ξ (c ξ) = 0) :
    ∀ ξ : X, L ξ (packetRotate β ψ lam t c ξ) = 0 :=
  packetRotate_linear_kernel β ψ lam t c L hc

example {X V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (c : X → V) (ξ : X) :
    ‖packetRotate β ψ lam t c ξ‖ = ‖c ξ‖ :=
  norm_packetRotate β ψ lam t c ξ

example {X V W : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W]
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ)
    (c : X → V) (ξ : X) (L : V →ₗ[ℂ] W) :
    ‖L (packetRotate β ψ lam t c ξ)‖ = ‖L (c ξ)‖ :=
  norm_linearMap_packetRotate β ψ lam t c ξ L

example {X V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
    (β : ℝ → ℝ) (ψ : X → ℝ) (lam t : ℝ) (c : X → V) (ξ : X) :
    ‖packetRotate β ψ lam t c ξ - c ξ‖ ≤
      (‖lam‖ * ‖β t‖ * ‖ψ ξ‖) * ‖c ξ‖ :=
  norm_packetRotate_sub_le β ψ lam t c ξ

example {X : Type*} [Neg X] (β : ℝ → ℝ) {ψ : X → ℝ}
    (hψ : ∀ ξ : X, ψ (-ξ) = -ψ ξ)
    (lam t : ℝ) {c : X → ℂ} (hc : ∀ ξ : X, c (-ξ) = conj (c ξ)) :
    ∀ ξ : X, packetRotate β ψ lam t c (-ξ) =
      conj (packetRotate β ψ lam t c ξ) :=
  packetRotate_reality β hψ lam t hc

example {X : Type*} {β : ℝ → ℝ} {ψ : X → ℝ} {t : ℝ} {ξ : X}
    (hβ : β t = 1) (hψ : ψ ξ = 1) {c : X → ℂ} (hc : c ξ ≠ 0)
    {lam eta : ℝ} (hlambda : |lam| < Real.pi / 4)
    (heta : |eta| < Real.pi / 4) (hne : lam ≠ eta) :
    packetRotate β ψ lam t c ξ ≠ packetRotate β ψ eta t c ξ :=
  packetRotate_active_separates hβ hψ hc hlambda heta hne

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {β : ℝ → ℝ} {ψ : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞
      (fun q : ℝ × (ℝ × E) => packetPhase β ψ q.1 q.2.1 q.2.2) :=
  contDiff_packetPhase_joint hβ hψ

example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {β : ℝ → ℝ} {ψ : E → ℝ}
    (hβ : ContDiff ℝ ∞ β) (hψ : ContDiff ℝ ∞ ψ) :
    ContDiff ℝ ∞
      (fun q : ℝ × (ℝ × E) => packetPhaseIncrement β ψ q.1 q.2.1 q.2.2) :=
  contDiff_packetPhaseIncrement_joint hβ hψ

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhase"
#check @MethbokeAddon.FDSNR3.packetPhase
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhase"
#print axioms MethbokeAddon.FDSNR3.packetPhase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhaseIncrement"
#check @MethbokeAddon.FDSNR3.packetPhaseIncrement
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhaseIncrement"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhaseIncrement"
#print axioms MethbokeAddon.FDSNR3.packetPhaseIncrement
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhaseIncrement"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetRotate"
#check @MethbokeAddon.FDSNR3.packetRotate
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetRotate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetRotate"
#print axioms MethbokeAddon.FDSNR3.packetRotate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetRotate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhase_eq_exp"
#check @MethbokeAddon.FDSNR3.packetPhase_eq_exp
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhase_eq_exp"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhase_eq_exp"
#print axioms MethbokeAddon.FDSNR3.packetPhase_eq_exp
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhase_eq_exp"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhase_zero_parameter"
#check @MethbokeAddon.FDSNR3.packetPhase_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhase_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhase_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.packetPhase_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhase_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhase_ne_zero"
#check @MethbokeAddon.FDSNR3.packetPhase_ne_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhase_ne_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhase_ne_zero"
#print axioms MethbokeAddon.FDSNR3.packetPhase_ne_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhase_ne_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_packetPhase"
#check @MethbokeAddon.FDSNR3.norm_packetPhase
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_packetPhase"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_packetPhase"
#print axioms MethbokeAddon.FDSNR3.norm_packetPhase
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_packetPhase"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhase_neg"
#check @MethbokeAddon.FDSNR3.packetPhase_neg
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhase_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhase_neg"
#print axioms MethbokeAddon.FDSNR3.packetPhase_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhase_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhase_eq_one_of_beta_zero"
#check @MethbokeAddon.FDSNR3.packetPhase_eq_one_of_beta_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhase_eq_one_of_beta_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhase_eq_one_of_beta_zero"
#print axioms MethbokeAddon.FDSNR3.packetPhase_eq_one_of_beta_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhase_eq_one_of_beta_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhase_eq_one_of_psi_zero"
#check @MethbokeAddon.FDSNR3.packetPhase_eq_one_of_psi_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhase_eq_one_of_psi_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhase_eq_one_of_psi_zero"
#print axioms MethbokeAddon.FDSNR3.packetPhase_eq_one_of_psi_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhase_eq_one_of_psi_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhase_at_normalization"
#check @MethbokeAddon.FDSNR3.packetPhase_at_normalization
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhase_at_normalization"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhase_at_normalization"
#print axioms MethbokeAddon.FDSNR3.packetPhase_at_normalization
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhase_at_normalization"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetPhaseIncrement_zero_parameter"
#check @MethbokeAddon.FDSNR3.packetPhaseIncrement_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetPhaseIncrement_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetPhaseIncrement_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.packetPhaseIncrement_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetPhaseIncrement_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_packetPhaseIncrement_le"
#check @MethbokeAddon.FDSNR3.norm_packetPhaseIncrement_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_packetPhaseIncrement_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_packetPhaseIncrement_le"
#print axioms MethbokeAddon.FDSNR3.norm_packetPhaseIncrement_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_packetPhaseIncrement_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_frequency_subset"
#check @MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_frequency_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_frequency_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_frequency_subset"
#print axioms MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_frequency_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_frequency_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_frequency"
#check @MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_frequency
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_frequency"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_frequency"
#print axioms MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_frequency
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_frequency"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_time_subset"
#check @MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_time_subset
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_time_subset"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_time_subset"
#print axioms MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_time_subset
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.tsupport_packetPhaseIncrement_time_subset"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_time"
#check @MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_time
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_time"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_time"
#print axioms MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_time
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.hasCompactSupport_packetPhaseIncrement_time"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetRotate_zero_parameter"
#check @MethbokeAddon.FDSNR3.packetRotate_zero_parameter
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetRotate_zero_parameter"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetRotate_zero_parameter"
#print axioms MethbokeAddon.FDSNR3.packetRotate_zero_parameter
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetRotate_zero_parameter"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetRotate_eq_of_beta_zero"
#check @MethbokeAddon.FDSNR3.packetRotate_eq_of_beta_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetRotate_eq_of_beta_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetRotate_eq_of_beta_zero"
#print axioms MethbokeAddon.FDSNR3.packetRotate_eq_of_beta_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetRotate_eq_of_beta_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetRotate_eq_of_psi_zero"
#check @MethbokeAddon.FDSNR3.packetRotate_eq_of_psi_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetRotate_eq_of_psi_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetRotate_eq_of_psi_zero"
#print axioms MethbokeAddon.FDSNR3.packetRotate_eq_of_psi_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetRotate_eq_of_psi_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetRotate_at_normalization"
#check @MethbokeAddon.FDSNR3.packetRotate_at_normalization
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetRotate_at_normalization"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetRotate_at_normalization"
#print axioms MethbokeAddon.FDSNR3.packetRotate_at_normalization
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetRotate_at_normalization"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetRotate_sub"
#check @MethbokeAddon.FDSNR3.packetRotate_sub
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetRotate_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetRotate_sub"
#print axioms MethbokeAddon.FDSNR3.packetRotate_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetRotate_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetRotate_linear_kernel"
#check @MethbokeAddon.FDSNR3.packetRotate_linear_kernel
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetRotate_linear_kernel"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetRotate_linear_kernel"
#print axioms MethbokeAddon.FDSNR3.packetRotate_linear_kernel
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetRotate_linear_kernel"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_packetRotate"
#check @MethbokeAddon.FDSNR3.norm_packetRotate
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_packetRotate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_packetRotate"
#print axioms MethbokeAddon.FDSNR3.norm_packetRotate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_packetRotate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_linearMap_packetRotate"
#check @MethbokeAddon.FDSNR3.norm_linearMap_packetRotate
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_linearMap_packetRotate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_linearMap_packetRotate"
#print axioms MethbokeAddon.FDSNR3.norm_linearMap_packetRotate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_linearMap_packetRotate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.norm_packetRotate_sub_le"
#check @MethbokeAddon.FDSNR3.norm_packetRotate_sub_le
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.norm_packetRotate_sub_le"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.norm_packetRotate_sub_le"
#print axioms MethbokeAddon.FDSNR3.norm_packetRotate_sub_le
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.norm_packetRotate_sub_le"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetRotate_reality"
#check @MethbokeAddon.FDSNR3.packetRotate_reality
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetRotate_reality"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetRotate_reality"
#print axioms MethbokeAddon.FDSNR3.packetRotate_reality
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetRotate_reality"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.packetRotate_active_separates"
#check @MethbokeAddon.FDSNR3.packetRotate_active_separates
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.packetRotate_active_separates"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.packetRotate_active_separates"
#print axioms MethbokeAddon.FDSNR3.packetRotate_active_separates
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.packetRotate_active_separates"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.contDiff_packetPhase_joint"
#check @MethbokeAddon.FDSNR3.contDiff_packetPhase_joint
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.contDiff_packetPhase_joint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.contDiff_packetPhase_joint"
#print axioms MethbokeAddon.FDSNR3.contDiff_packetPhase_joint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.contDiff_packetPhase_joint"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_joint"
#check @MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_joint
#eval IO.println "TYPE_END:MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_joint"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_joint"
#print axioms MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_joint
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSNR3.contDiff_packetPhaseIncrement_joint"

