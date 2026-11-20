import FDSNSmoothSmallness.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false


set_option autoImplicit false

noncomputable section

open Set
open scoped ContDiff
open MethbokeAddon.FDSN

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

example (G : ℝ × E → F) (hG : ContDiff ℝ ∞ G) (n : ℕ) :
    ContDiff ℝ ∞ (fun p : ℝ × E =>
      iteratedFDeriv ℝ n (fun z : E => G (p.1, z)) p.2) :=
  contDiff_spatial_iteratedFDeriv G hG n

example (G : ℝ × E → F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ z : E, G (0, z) = 0)
    (K : Set E) (hK : IsCompact K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      ∀ z ∈ K, ‖G (lambda, z)‖ ≤ C * ‖lambda‖ :=
  smooth_family_uniform_linear_bound G hG hzero K hK

example (G : ℝ × E → F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ z : E, G (0, z) = 0)
    (K : Set E) (hK : IsCompact K) (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      ∀ z ∈ K,
        ‖iteratedFDeriv ℝ n (fun y : E => G (lambda, y)) z‖ ≤ C * ‖lambda‖ :=
  smooth_family_iteratedFDeriv_linear_bound G hG hzero K hK n

example (G : ℝ × E → F) (hG : ContDiff ℝ ∞ G)
    (hzero : ∀ z : E, G (0, z) = 0)
    (K : Set E) (hK : IsCompact K) (r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ lambda : ℝ, ‖lambda‖ ≤ 1 →
      ∀ n : ℕ, n ≤ r → ∀ z ∈ K,
        ‖iteratedFDeriv ℝ n (fun y : E => G (lambda, y)) z‖ ≤ C * ‖lambda‖ :=
  smooth_family_finite_order_linear_bound G hG hzero K hK r

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.contDiff_spatial_iteratedFDeriv"
#check @MethbokeAddon.FDSN.contDiff_spatial_iteratedFDeriv
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.contDiff_spatial_iteratedFDeriv"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.contDiff_spatial_iteratedFDeriv"
#print axioms MethbokeAddon.FDSN.contDiff_spatial_iteratedFDeriv
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.contDiff_spatial_iteratedFDeriv"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.smooth_family_uniform_linear_bound"
#check @MethbokeAddon.FDSN.smooth_family_uniform_linear_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.smooth_family_uniform_linear_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.smooth_family_uniform_linear_bound"
#print axioms MethbokeAddon.FDSN.smooth_family_uniform_linear_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.smooth_family_uniform_linear_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.smooth_family_iteratedFDeriv_linear_bound"
#check @MethbokeAddon.FDSN.smooth_family_iteratedFDeriv_linear_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.smooth_family_iteratedFDeriv_linear_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.smooth_family_iteratedFDeriv_linear_bound"
#print axioms MethbokeAddon.FDSN.smooth_family_iteratedFDeriv_linear_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.smooth_family_iteratedFDeriv_linear_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.smooth_family_finite_order_linear_bound"
#check @MethbokeAddon.FDSN.smooth_family_finite_order_linear_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.smooth_family_finite_order_linear_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.smooth_family_finite_order_linear_bound"
#print axioms MethbokeAddon.FDSN.smooth_family_finite_order_linear_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.smooth_family_finite_order_linear_bound"

