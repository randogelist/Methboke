import FDSNNonvanishing.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

open scoped ContDiff Topology

example {s t T : ℝ} {g : ℝ → ℂ}
    (hst : s < t) (htT : t < T)
    (hg : ContinuousAt g t) (hgt : g t ≠ 0) :
    ∃ a b : ℝ,
      s < a ∧ a < t ∧ t < b ∧ b < T ∧
      ∀ u : ℝ, u ∈ Set.Icc a b → g u ≠ 0 :=
  MethbokeAddon.FDSN.exists_nonvanishing_closed_slab hst htT hg hgt

example {s t T : ℝ} {g : ℝ → ℂ}
    (hst : s < t) (htT : t < T)
    (hg : ContinuousAt g t) (hgt : g t ≠ 0) :
    ∃ β : ℝ → ℝ,
      ContDiff ℝ ∞ β ∧
      HasCompactSupport β ∧
      tsupport β ⊆ Set.Ioo s T ∧
      β t = 1 ∧
      (∀ u : ℝ, 0 ≤ β u ∧ β u ≤ 1) ∧
      ∀ u : ℝ, u ∈ tsupport β → g u ≠ 0 :=
  MethbokeAddon.FDSN.exists_normalized_bump_on_nonvanishing_slab hst htT hg hgt



#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.exists_nonvanishing_closed_slab"
#check @MethbokeAddon.FDSN.exists_nonvanishing_closed_slab
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.exists_nonvanishing_closed_slab"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.exists_nonvanishing_closed_slab"
#print axioms MethbokeAddon.FDSN.exists_nonvanishing_closed_slab
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.exists_nonvanishing_closed_slab"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.exists_normalized_bump_on_nonvanishing_slab"
#check @MethbokeAddon.FDSN.exists_normalized_bump_on_nonvanishing_slab
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.exists_normalized_bump_on_nonvanishing_slab"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.exists_normalized_bump_on_nonvanishing_slab"
#print axioms MethbokeAddon.FDSN.exists_normalized_bump_on_nonvanishing_slab
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.exists_normalized_bump_on_nonvanishing_slab"

