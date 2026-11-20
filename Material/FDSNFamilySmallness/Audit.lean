import FDSNFamilySmallness.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false
set_option pp.fullNames true
set_option pp.universes true

open Set SingularClosure MethbokeAddon.FDSN
open scoped BigOperators ContDiff

noncomputable section

example
    (r : ℕ) (a b : ℝ) (hab : a ≤ b) (V : Velocity) (C : ℝ)
    (hbound : ∀ n : ℕ, n ≤ r → ∀ z ∈ Icc a b ×ˢ unitCube,
      ‖iteratedFDeriv ℝ n (fun y : ℝ × Vec => V y.1 y.2) z‖ ≤ C) :
    spacetimeCrNorm r a b V ≤ ((r + 1 : ℕ) : ℝ) * C :=
  spacetimeCrNorm_le_of_derivative_bound r a b hab V C hbound

example
    (G : ℝ × (ℝ × Vec) → Vec) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ z : ℝ × Vec, G (0, z) = 0)
    (a b : ℝ) (hab : a ≤ b) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      spacetimeCrNorm r a b (fun t x => G (lambda, (t, x))) ≤ C * ‖lambda‖ :=
  smooth_family_spacetimeCrNorm_linear_bound G hG hzero a b hab r

example
    (a b ε : ℝ) (hab : a ≤ b) (u F : Velocity) (U G : ℝ → Velocity)
    (hU : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      (U q.1 - u) q.2.1 q.2.2))
    (hG : ContDiff ℝ ∞ (fun q : ℝ × (ℝ × Vec) =>
      (G q.1 - F) q.2.1 q.2.2))
    (hU0 : U 0 = u) (hG0 : G 0 = F) :
    SmoothSmallness a b ε u F U G :=
  smooth_corrections_imply_smallness a b ε hab u F U G hU hG hU0 hG0




end

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.spacetimeCrNorm_le_of_derivative_bound"
#check @MethbokeAddon.FDSN.spacetimeCrNorm_le_of_derivative_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.spacetimeCrNorm_le_of_derivative_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.spacetimeCrNorm_le_of_derivative_bound"
#print axioms MethbokeAddon.FDSN.spacetimeCrNorm_le_of_derivative_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.spacetimeCrNorm_le_of_derivative_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.smooth_family_spacetimeCrNorm_linear_bound"
#check @MethbokeAddon.FDSN.smooth_family_spacetimeCrNorm_linear_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.smooth_family_spacetimeCrNorm_linear_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.smooth_family_spacetimeCrNorm_linear_bound"
#print axioms MethbokeAddon.FDSN.smooth_family_spacetimeCrNorm_linear_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.smooth_family_spacetimeCrNorm_linear_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.smooth_corrections_imply_smallness"
#check @MethbokeAddon.FDSN.smooth_corrections_imply_smallness
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.smooth_corrections_imply_smallness"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.smooth_corrections_imply_smallness"
#print axioms MethbokeAddon.FDSN.smooth_corrections_imply_smallness
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.smooth_corrections_imply_smallness"

