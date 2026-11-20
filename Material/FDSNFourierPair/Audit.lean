import FDSNFourierPair.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators
open SingularClosure MethbokeAddon.FDSN

noncomputable section

/- Exact consumer types plus literal operation checks. -/
example : Frequency → ℂ → Frequency → ℂ := pairMultiplier
example : Frequency → ℂ → FourierCoeff → FourierCoeff := pairRotate
example (a : Frequency) (z : ℂ) (k : Frequency) :
    pairMultiplier a z k = if k = a then z else if k = -a then star z else 1 := rfl
example (a : Frequency) (z : ℂ) (c : FourierCoeff) (k : Frequency) (i : Fin 3) :
    pairRotate a z c k i = pairMultiplier a z k * c k i := rfl

example {a : Frequency} (ha : a ≠ 0) : a ≠ -a := frequency_ne_neg_self ha
example (a : Frequency) (z : ℂ) : pairMultiplier a z a = z := pairMultiplier_at a z
example {a : Frequency} (ha : a ≠ 0) (z : ℂ) :
    pairMultiplier a z (-a) = star z := pairMultiplier_at_neg ha z
example {a k : Frequency} (z : ℂ) (hka : k ≠ a) (hkna : k ≠ -a) :
    pairMultiplier a z k = 1 := pairMultiplier_off z hka hkna
example {a : Frequency} (ha : a ≠ 0) (z : ℂ) :
    pairMultiplier a z 0 = 1 := pairMultiplier_at_zero ha z
example {a : Frequency} (ha : a ≠ 0) (z : ℂ) (k : Frequency) :
    pairMultiplier a z (-k) = star (pairMultiplier a z k) := pairMultiplier_neg ha z k
example (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1) (k : Frequency) :
    ‖pairMultiplier a z k‖ = 1 := pairMultiplier_norm a hz k
example (a k : Frequency) : pairMultiplier a 1 k = 1 := pairMultiplier_one a k
example (a : Frequency) (c : FourierCoeff) : pairRotate a 1 c = c := pairRotate_one a c
example (a : Frequency) (z : ℂ) (c : FourierCoeff) :
    pairRotate a z c a = z • c a := pairRotate_at a z c
example {a : Frequency} (ha : a ≠ 0) (z : ℂ) (c : FourierCoeff) :
    pairRotate a z c (-a) = star z • c (-a) := pairRotate_at_neg ha z c
example {a k : Frequency} (z : ℂ) (c : FourierCoeff)
    (hka : k ≠ a) (hkna : k ≠ -a) : pairRotate a z c k = c k :=
  pairRotate_off z c hka hkna
example {a : Frequency} (ha : a ≠ 0) (z : ℂ) (c : FourierCoeff) :
    pairRotate a z c 0 = c 0 := pairRotate_mean ha z c
example {a : Frequency} (ha : a ≠ 0) (z : ℂ) {c : FourierCoeff}
    (hc : SpectralReality c) : SpectralReality (pairRotate a z c) := pairRotate_reality ha z hc
example (a : Frequency) (z : ℂ) {c : FourierCoeff} (hc : SpectralSolenoidal c) :
    SpectralSolenoidal (pairRotate a z c) := pairRotate_solenoidal a z hc
example (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1) (c : FourierCoeff)
    (k : Frequency) (i : Fin 3) : ‖pairRotate a z c k i‖ = ‖c k i‖ :=
  pairRotate_component_norm a hz c k i
example (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1) (c : FourierCoeff)
    (k : Frequency) (L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ) :
    ‖L (pairRotate a z c k)‖ = ‖L (c k)‖ := pairRotate_observable_norm a hz c k L
example (a : Frequency) {z : ℂ} (hz : ‖z‖ = 1)
    (c : FourierCoeff) (w : Frequency → ℝ) :
    (∑' k : Frequency, w k * ∑ i : Fin 3, ‖pairRotate a z c k i‖ ^ 2) =
      ∑' k : Frequency, w k * ∑ i : Fin 3, ‖c k i‖ ^ 2 :=
  pairRotate_weighted_power_sum a hz c w
example {a : Frequency} (ha : a ≠ 0) {z : ℂ} (hz : ‖z‖ = 1)
    (c : FourierCoeff) (hr : SpectralReality c) (hs : SpectralSolenoidal c) :
    SpectralReality (pairRotate a z c) ∧
    SpectralSolenoidal (pairRotate a z c) ∧
    pairRotate a z c 0 = c 0 ∧
    (∀ k : Frequency, ∀ L : (Fin 3 → ℂ) →ₗ[ℂ] ℂ,
      ‖L (pairRotate a z c k)‖ = ‖L (c k)‖) :=
  PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_CONSTRAINTS ha hz c hr hs


end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairMultiplier"
#check @MethbokeAddon.FDSN.pairMultiplier
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairMultiplier"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairMultiplier"
#print axioms MethbokeAddon.FDSN.pairMultiplier
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairMultiplier"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate"
#check @MethbokeAddon.FDSN.pairRotate
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate"
#print axioms MethbokeAddon.FDSN.pairRotate
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.frequency_ne_neg_self"
#check @MethbokeAddon.FDSN.frequency_ne_neg_self
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.frequency_ne_neg_self"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.frequency_ne_neg_self"
#print axioms MethbokeAddon.FDSN.frequency_ne_neg_self
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.frequency_ne_neg_self"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairMultiplier_at"
#check @MethbokeAddon.FDSN.pairMultiplier_at
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairMultiplier_at"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairMultiplier_at"
#print axioms MethbokeAddon.FDSN.pairMultiplier_at
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairMultiplier_at"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairMultiplier_at_neg"
#check @MethbokeAddon.FDSN.pairMultiplier_at_neg
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairMultiplier_at_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairMultiplier_at_neg"
#print axioms MethbokeAddon.FDSN.pairMultiplier_at_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairMultiplier_at_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairMultiplier_off"
#check @MethbokeAddon.FDSN.pairMultiplier_off
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairMultiplier_off"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairMultiplier_off"
#print axioms MethbokeAddon.FDSN.pairMultiplier_off
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairMultiplier_off"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairMultiplier_at_zero"
#check @MethbokeAddon.FDSN.pairMultiplier_at_zero
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairMultiplier_at_zero"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairMultiplier_at_zero"
#print axioms MethbokeAddon.FDSN.pairMultiplier_at_zero
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairMultiplier_at_zero"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairMultiplier_neg"
#check @MethbokeAddon.FDSN.pairMultiplier_neg
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairMultiplier_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairMultiplier_neg"
#print axioms MethbokeAddon.FDSN.pairMultiplier_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairMultiplier_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairMultiplier_norm"
#check @MethbokeAddon.FDSN.pairMultiplier_norm
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairMultiplier_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairMultiplier_norm"
#print axioms MethbokeAddon.FDSN.pairMultiplier_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairMultiplier_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairMultiplier_one"
#check @MethbokeAddon.FDSN.pairMultiplier_one
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairMultiplier_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairMultiplier_one"
#print axioms MethbokeAddon.FDSN.pairMultiplier_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairMultiplier_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_one"
#check @MethbokeAddon.FDSN.pairRotate_one
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_one"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_one"
#print axioms MethbokeAddon.FDSN.pairRotate_one
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_one"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_at"
#check @MethbokeAddon.FDSN.pairRotate_at
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_at"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_at"
#print axioms MethbokeAddon.FDSN.pairRotate_at
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_at"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_at_neg"
#check @MethbokeAddon.FDSN.pairRotate_at_neg
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_at_neg"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_at_neg"
#print axioms MethbokeAddon.FDSN.pairRotate_at_neg
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_at_neg"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_off"
#check @MethbokeAddon.FDSN.pairRotate_off
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_off"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_off"
#print axioms MethbokeAddon.FDSN.pairRotate_off
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_off"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_mean"
#check @MethbokeAddon.FDSN.pairRotate_mean
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_mean"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_mean"
#print axioms MethbokeAddon.FDSN.pairRotate_mean
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_mean"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_reality"
#check @MethbokeAddon.FDSN.pairRotate_reality
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_reality"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_reality"
#print axioms MethbokeAddon.FDSN.pairRotate_reality
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_reality"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_solenoidal"
#check @MethbokeAddon.FDSN.pairRotate_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_solenoidal"
#print axioms MethbokeAddon.FDSN.pairRotate_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_component_norm"
#check @MethbokeAddon.FDSN.pairRotate_component_norm
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_component_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_component_norm"
#print axioms MethbokeAddon.FDSN.pairRotate_component_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_component_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_observable_norm"
#check @MethbokeAddon.FDSN.pairRotate_observable_norm
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_observable_norm"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_observable_norm"
#print axioms MethbokeAddon.FDSN.pairRotate_observable_norm
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_observable_norm"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.pairRotate_weighted_power_sum"
#check @MethbokeAddon.FDSN.pairRotate_weighted_power_sum
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.pairRotate_weighted_power_sum"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.pairRotate_weighted_power_sum"
#print axioms MethbokeAddon.FDSN.pairRotate_weighted_power_sum
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.pairRotate_weighted_power_sum"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_CONSTRAINTS"
#check @MethbokeAddon.FDSN.PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_CONSTRAINTS
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_CONSTRAINTS"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_CONSTRAINTS"
#print axioms MethbokeAddon.FDSN.PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_CONSTRAINTS
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.PAIR_ROTATION_PRESERVES_PERIODIC_SPECTRAL_CONSTRAINTS"

