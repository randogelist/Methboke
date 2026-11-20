import FDSNBump.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open scoped ContDiff Topology

/- Literal consumer of the complete normalized-time-bump contract. -/
example {s t T : ℝ} (hst : s < t) (htT : t < T) :
    ∃ β : ℝ → ℝ,
      ContDiff ℝ ∞ β ∧
      HasCompactSupport β ∧
      tsupport β ⊆ Set.Ioo s T ∧
      β t = 1 ∧
      ∀ u : ℝ, 0 ≤ β u ∧ β u ≤ 1 :=
  MethbokeAddon.FDSN.exists_normalized_time_bump hst htT


#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.exists_normalized_time_bump"
#check @MethbokeAddon.FDSN.exists_normalized_time_bump
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.exists_normalized_time_bump"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.exists_normalized_time_bump"
#print axioms MethbokeAddon.FDSN.exists_normalized_time_bump
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.exists_normalized_time_bump"

