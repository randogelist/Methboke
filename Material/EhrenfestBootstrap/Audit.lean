import EhrenfestBootstrap.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independent exact consumer types; external evidence pending. -/

open Set Filter
open scoped Topology

namespace MethbokeAddon.EhrenfestObstruction

-- Independently stated consumers for external cached CI. No local execution.

example {x : ℝ} (h0 : 0 ≤ x) (h1 : x ≤ 1) : x ^ 3 ≤ x :=
  cubic_le_self_of_mem_unit_interval h0 h1

example (C epsilon t : ℝ) :
    HasDerivAt (fun s : ℝ => 2 * epsilon * Real.exp ((2 * C + 1) * s))
      ((2 * C + 1) * (2 * epsilon * Real.exp ((2 * C + 1) * t))) t :=
  small_forcing_fence_hasDerivAt C epsilon t

example {D d : ℝ → ℝ} {C epsilon T : ℝ}
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hsmall : 2 * epsilon * Real.exp ((2 * C + 1) * T) ≤ 1)
    (hD : ContinuousOn D (Icc 0 T))
    (hinit : D 0 ≤ 0)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt D (d t) (Ici 0) t)
    (hguard : ∀ t ∈ Ico 0 T, D t ≤ 1 →
      d t ≤ C * (D t + (D t) ^ 3) + epsilon) :
    ∀ t ∈ Icc 0 T,
      D t ≤ 2 * epsilon * Real.exp ((2 * C + 1) * t) ∧ D t ≤ 1 :=
  guarded_cubic_small_forcing_bound hC hepsilon hsmall hD hinit hderiv hguard

example {D d : ℝ → ℝ} {C epsilon T : ℝ}
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hsmall : 2 * epsilon * Real.exp ((2 * C + 1) * T) ≤ 1)
    (hD : ContinuousOn D (Icc 0 T))
    (hnonneg : ∀ t ∈ Icc 0 T, 0 ≤ D t)
    (hinit : D 0 ≤ 0)
    (hderiv : ∀ t ∈ Ico 0 T, HasDerivWithinAt D (d t) (Ici 0) t)
    (hguard : ∀ t ∈ Ico 0 T, D t ≤ 1 →
      d t ≤ C * (D t + (D t) ^ 3) + epsilon) :
    ∀ t ∈ Icc 0 T, D t ≤ gronwallBound 0 (2 * C) epsilon t :=
  guarded_cubic_small_forcing_gronwall
    hC hepsilon hsmall hD hnonneg hinit hderiv hguard

example {D d : ℕ → ℝ → ℝ} {epsilon : ℕ → ℝ} {C T : ℝ}
    (hC : 0 ≤ C)
    (hepsilon : ∀ᶠ n in atTop, 0 < epsilon n)
    (hlim : Tendsto epsilon atTop (𝓝 0))
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hinit : ∀ n, D n 0 ≤ 0)
    (hderiv : ∀ n, ∀ t ∈ Ico 0 T,
      HasDerivWithinAt (D n) (d n t) (Ici 0) t)
    (hguard : ∀ n, ∀ t ∈ Ico 0 T, D n t ≤ 1 →
      d n t ≤ C * (D n t + (D n t) ^ 3) + epsilon n) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, D n t ≤ 1 :=
  eventually_guarded_cubic_unit_bound hC hepsilon hlim hD hinit hderiv hguard

example {D d : ℝ → ℝ} {C epsilon T : ℝ}
    (hC : 0 ≤ C) (hepsilon : 0 < epsilon)
    (hsmall : 2 * epsilon * Real.exp ((2 * C + 1) * T) ≤ 1)
    (hD : ContinuousOn D (Icc 0 T))
    (hinit : D 0 ≤ 0)
    (hderiv : ∀ t ∈ Ioo 0 T, HasDerivAt D (d t) t)
    (hguard : ∀ t ∈ Ioo 0 T, D t ≤ 1 →
      d t ≤ C * (D t + (D t) ^ 3) + epsilon) :
    ∀ t ∈ Icc 0 T,
      D t ≤ 2 * epsilon * Real.exp ((2 * C + 1) * t) ∧ D t ≤ 1 :=
  guarded_cubic_small_forcing_bound_interior hC hepsilon hsmall hD hinit hderiv hguard

example {D d : ℕ → ℝ → ℝ} {epsilon : ℕ → ℝ} {C T : ℝ}
    (hC : 0 ≤ C)
    (hepsilon : ∀ᶠ n in atTop, 0 < epsilon n)
    (hlim : Tendsto epsilon atTop (𝓝 0))
    (hD : ∀ n, ContinuousOn (D n) (Icc 0 T))
    (hinit : ∀ n, D n 0 ≤ 0)
    (hderiv : ∀ n, ∀ t ∈ Ioo 0 T, HasDerivAt (D n) (d n t) t)
    (hguard : ∀ n, ∀ t ∈ Ioo 0 T, D n t ≤ 1 →
      d n t ≤ C * (D n t + (D n t) ^ 3) + epsilon n) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc 0 T, D n t ≤ 1 :=
  eventually_guarded_cubic_unit_bound_interior hC hepsilon hlim hD hinit hderiv hguard


end MethbokeAddon.EhrenfestObstruction


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.cubic_le_self_of_mem_unit_interval"
#check @MethbokeAddon.EhrenfestObstruction.cubic_le_self_of_mem_unit_interval
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.cubic_le_self_of_mem_unit_interval"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.cubic_le_self_of_mem_unit_interval"
#print axioms MethbokeAddon.EhrenfestObstruction.cubic_le_self_of_mem_unit_interval
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.cubic_le_self_of_mem_unit_interval"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.small_forcing_fence_hasDerivAt"
#check @MethbokeAddon.EhrenfestObstruction.small_forcing_fence_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.small_forcing_fence_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.small_forcing_fence_hasDerivAt"
#print axioms MethbokeAddon.EhrenfestObstruction.small_forcing_fence_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.small_forcing_fence_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound"
#check @MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound"
#print axioms MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_gronwall"
#check @MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_gronwall
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_gronwall"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_gronwall"
#print axioms MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_gronwall
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_gronwall"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound"
#check @MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound"
#print axioms MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound_interior"
#check @MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound_interior
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound_interior"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound_interior"
#print axioms MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound_interior
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.guarded_cubic_small_forcing_bound_interior"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound_interior"
#check @MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound_interior
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound_interior"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound_interior"
#print axioms MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound_interior
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.eventually_guarded_cubic_unit_bound_interior"

