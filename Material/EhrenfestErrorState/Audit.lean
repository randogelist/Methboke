import EhrenfestErrorState.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/-! Independent exact consumer types; external evidence pending. -/


section Consumer1
open Set Filter SingularClosure
open MethbokeAddon.WeakFouriermanB

namespace MethbokeAddon.EhrenfestObstruction

-- Independently stated consumer types for authorized external cached CI.

example (z w : ℂ) :
    Complex.normSq (z + w) ≤ 2 * Complex.normSq z + 2 * Complex.normSq w :=
  complex_normSq_add_le_twice z w

example (N : ℕ) (c v : FourierCoeff) :
    coefficientDissipation N (c + v) ≤
      2 * coefficientDissipation N c + 2 * coefficientDissipation N v :=
  coefficientDissipation_add_le_twice N c v

example (N : ℕ) (c v : FourierCoeff) :
    coefficientDissipation N c ≤
      2 * coefficientDissipation N (c - v) + 2 * coefficientDissipation N v :=
  coefficientDissipation_le_error_plus_reference N c v

example (N : ℕ) (c : FourierCoeff) :
    coefficientDissipation N (cutoffCoeff N c) = coefficientDissipation N c :=
  coefficientDissipation_cutoff_eq N c

example (N : ℕ) : coefficientDissipation N (0 : FourierCoeff) = 0 :=
  coefficientDissipation_zero_eq N

example {c v : FourierCoeff} (hc : SpectralReality c) (hv : SpectralReality v) :
    SpectralReality (c - v) := spectralReality_sub hc hv

example {c v : FourierCoeff} (hc : SpectralSolenoidal c) (hv : SpectralSolenoidal v) :
    SpectralSolenoidal (c - v) := spectralSolenoidal_sub hc hv

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (u : Velocity) (n : ℕ) (t : ℝ) :
    canonicalErrorCoeff ν hν a u n t =
      (canonicalGalerkinSolution ν hν a.val a.property (n + 1)).coeff t -
        cutoffCoeff (n + 1) (datumFourierCoeff (u t)) := rfl

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity)
    (hinit : u 0 = a.val) (n : ℕ) : canonicalErrorCoeff ν hν a u n 0 = 0 :=
  canonicalErrorCoeff_initial ν hν a u hinit n

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (n : ℕ) :
    canonicalErrorCoeff ν hν a u n 0 = 0 :=
  canonicalErrorCoeff_initial_front ν hν a S u p H n

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t)
    (k : Frequency) (hk : k ∉ cutoffModes (n + 1)) (i : Fin 3) :
    canonicalErrorCoeff ν hν a u n t k i = 0 :=
  canonicalErrorCoeff_support ν hν a u n t ht k hk i

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    SpectralReality (canonicalErrorCoeff ν hν a u n t) :=
  canonicalErrorCoeff_reality ν hν a u n t ht

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity)
    (n : ℕ) (t : ℝ) (ht : 0 ≤ t) (hu : SmoothSigmaZero (u t)) :
    SpectralSolenoidal (canonicalErrorCoeff ν hν a u n t) :=
  canonicalErrorCoeff_solenoidal ν hν a u n t ht hu

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p)
    (n : ℕ) (t : ℝ) (ht : t ∈ Ico (0 : ℝ) S) :
    SpectralSolenoidal (canonicalErrorCoeff ν hν a u n t) :=
  canonicalErrorCoeff_solenoidal_front ν hν a S u p H n t ht

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity)
    (hinit : u 0 = a.val) (n : ℕ) :
    coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n 0) = 0 :=
  canonical_error_initial_dissipation ν hν a u hinit n

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity) (n : ℕ) (t : ℝ) :
    canonicalEnstrophy ν hν a n t ≤
      coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t) +
        coefficientDissipation (n + 1) (datumFourierCoeff (u t)) :=
  canonical_enstrophy_le_error_plus_reference ν hν a u n t

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum) (u : Velocity) (T K : ℝ)
    (herror : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t) ≤ 1)
    (hreference : ∀ n t, t ∈ Icc (0 : ℝ) T →
      coefficientDissipation (n + 1) (datumFourierCoeff (u t)) ≤ K) :
    ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      canonicalEnstrophy ν hν a n t ≤ 1 + K :=
  eventual_canonical_slab_bound_of_error_and_reference ν hν a u T K herror hreference

example (ν : ℝ) (hν : 0 < ν) (a : SmoothDatum)
    (S T : ℝ) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν S a.val u p) (hTS : T < S)
    (herror : ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      coefficientDissipation (n + 1) (canonicalErrorCoeff ν hν a u n t) ≤ 1) :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ t ∈ Icc (0 : ℝ) T,
      canonicalEnstrophy ν hν a n t ≤ C :=
  smooth_front_eventual_slab_bound_of_unit_error ν hν a S T u p H hTS herror


end MethbokeAddon.EhrenfestObstruction
end Consumer1


#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.complex_normSq_add_le_twice"
#check @MethbokeAddon.EhrenfestObstruction.complex_normSq_add_le_twice
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.complex_normSq_add_le_twice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.complex_normSq_add_le_twice"
#print axioms MethbokeAddon.EhrenfestObstruction.complex_normSq_add_le_twice
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.complex_normSq_add_le_twice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_add_le_twice"
#check @MethbokeAddon.EhrenfestObstruction.coefficientDissipation_add_le_twice
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_add_le_twice"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_add_le_twice"
#print axioms MethbokeAddon.EhrenfestObstruction.coefficientDissipation_add_le_twice
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_add_le_twice"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_le_error_plus_reference"
#check @MethbokeAddon.EhrenfestObstruction.coefficientDissipation_le_error_plus_reference
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_le_error_plus_reference"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_le_error_plus_reference"
#print axioms MethbokeAddon.EhrenfestObstruction.coefficientDissipation_le_error_plus_reference
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_le_error_plus_reference"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_cutoff_eq"
#check @MethbokeAddon.EhrenfestObstruction.coefficientDissipation_cutoff_eq
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_cutoff_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_cutoff_eq"
#print axioms MethbokeAddon.EhrenfestObstruction.coefficientDissipation_cutoff_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_cutoff_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_zero_eq"
#check @MethbokeAddon.EhrenfestObstruction.coefficientDissipation_zero_eq
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_zero_eq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_zero_eq"
#print axioms MethbokeAddon.EhrenfestObstruction.coefficientDissipation_zero_eq
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.coefficientDissipation_zero_eq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.spectralReality_sub"
#check @MethbokeAddon.EhrenfestObstruction.spectralReality_sub
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.spectralReality_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.spectralReality_sub"
#print axioms MethbokeAddon.EhrenfestObstruction.spectralReality_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.spectralReality_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.spectralSolenoidal_sub"
#check @MethbokeAddon.EhrenfestObstruction.spectralSolenoidal_sub
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.spectralSolenoidal_sub"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.spectralSolenoidal_sub"
#print axioms MethbokeAddon.EhrenfestObstruction.spectralSolenoidal_sub
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.spectralSolenoidal_sub"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial"
#check @MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial"
#print axioms MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial_front"
#check @MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial_front
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial_front"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial_front"
#print axioms MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial_front
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_initial_front"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_support"
#check @MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_support
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_support"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_support"
#print axioms MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_support
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_support"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_reality"
#check @MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_reality
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_reality"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_reality"
#print axioms MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_reality
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_reality"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal"
#check @MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal"
#print axioms MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal_front"
#check @MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal_front
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal_front"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal_front"
#print axioms MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal_front
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonicalErrorCoeff_solenoidal_front"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_error_initial_dissipation"
#check @MethbokeAddon.EhrenfestObstruction.canonical_error_initial_dissipation
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_error_initial_dissipation"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_error_initial_dissipation"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_error_initial_dissipation
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_error_initial_dissipation"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_error_plus_reference"
#check @MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_error_plus_reference
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_error_plus_reference"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_error_plus_reference"
#print axioms MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_error_plus_reference
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.canonical_enstrophy_le_error_plus_reference"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.eventual_canonical_slab_bound_of_error_and_reference"
#check @MethbokeAddon.EhrenfestObstruction.eventual_canonical_slab_bound_of_error_and_reference
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.eventual_canonical_slab_bound_of_error_and_reference"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.eventual_canonical_slab_bound_of_error_and_reference"
#print axioms MethbokeAddon.EhrenfestObstruction.eventual_canonical_slab_bound_of_error_and_reference
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.eventual_canonical_slab_bound_of_error_and_reference"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_front_eventual_slab_bound_of_unit_error"
#check @MethbokeAddon.EhrenfestObstruction.smooth_front_eventual_slab_bound_of_unit_error
#eval IO.println "TYPE_END:MethbokeAddon.EhrenfestObstruction.smooth_front_eventual_slab_bound_of_unit_error"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.EhrenfestObstruction.smooth_front_eventual_slab_bound_of_unit_error"
#print axioms MethbokeAddon.EhrenfestObstruction.smooth_front_eventual_slab_bound_of_unit_error
#eval IO.println "AXIOMS_END:MethbokeAddon.EhrenfestObstruction.smooth_front_eventual_slab_bound_of_unit_error"
