import FDSNModalEnergy.Endpoint

set_option pp.universes true
set_option pp.fullNames true
set_option autoImplicit false

/- Explicit full-type consumers; root supplies imports and audit sentinels. -/

noncomputable section
open Set
open MethbokeAddon.FDSN

example : ∀ no pressure reconstruction and no continuity of the phase
coefficient beyond the stated derivative and energy conditions.
-/

noncomputable section
open Set

namespace MethbokeAddon.FDSN

theorem complex_normSq_hasDerivAt {z : ℝ → ℂ} {dz : ℂ} {t : ℝ}
    (hz : HasDerivAt z dz t),
    HasDerivAt (fun s => Complex.normSq (z s))
      (2 * (star (z t) * dz).re) t :=
  @MethbokeAddon.FDSN.needs

example : ∀ {z : ℝ → ℂ} {dz : ℂ} {t : ℝ}
    (hz : HasDerivAt z dz t),
    HasDerivAt (fun s => Complex.normSq (z s))
      (2 * (star (z t) * dz).re) t :=
  @MethbokeAddon.FDSN.complex_normSq_hasDerivAt

example : ∀ {z : ℝ → ℂ} {a : ℂ} {t : ℝ}
    (hz : HasDerivAt z (-a * z t) t),
    HasDerivAt (fun s => Complex.normSq (z s))
      (-2 * a.re * Complex.normSq (z t)) t :=
  @MethbokeAddon.FDSN.complex_damped_normSq_hasDerivAt

example : ∀ (z a : ℝ → ℂ) (s t : ℝ)
    (hc : ContinuousOn z (Icc s t))
    (hd : ∀ r ∈ Ioo s t, HasDerivAt z (-a r * z r) r)
    (ha : ∀ r ∈ Ioo s t, 0 ≤ (a r).re),
    AntitoneOn (fun r => Complex.normSq (z r)) (Icc s t) :=
  @MethbokeAddon.FDSN.complex_damped_energy_antitone

example : ∀ (z a : ℝ → ℂ) (s t : ℝ) (hst : s ≤ t)
    (hc : ContinuousOn z (Icc s t))
    (hd : ∀ r ∈ Ioo s t, HasDerivAt z (-a r * z r) r)
    (ha : ∀ r ∈ Ioo s t, 0 ≤ (a r).re) (hz : z s = 0),
    ∀ r ∈ Icc s t, z r = 0 :=
  @MethbokeAddon.FDSN.complex_damped_zero_on_Icc

example : ∀ (z f : ℂ),
    2 * (star z * f).re ≤ Complex.normSq z + Complex.normSq f :=
  @MethbokeAddon.FDSN.complex_work_le_normSq

example : ∀ (z N f : ℂ) (d : ℝ) (hd : 0 ≤ d) (hN : (star z * N).re = 0),
    2 * (star z * (-((d : ℂ) * z) - N + f)).re ≤
      Complex.normSq z + Complex.normSq f :=
  @MethbokeAddon.FDSN.complex_forced_energy_bound

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.complex_normSq_hasDerivAt"
#check @MethbokeAddon.FDSN.complex_normSq_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.complex_normSq_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.complex_normSq_hasDerivAt"
#print axioms MethbokeAddon.FDSN.complex_normSq_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.complex_normSq_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.complex_damped_normSq_hasDerivAt"
#check @MethbokeAddon.FDSN.complex_damped_normSq_hasDerivAt
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.complex_damped_normSq_hasDerivAt"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.complex_damped_normSq_hasDerivAt"
#print axioms MethbokeAddon.FDSN.complex_damped_normSq_hasDerivAt
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.complex_damped_normSq_hasDerivAt"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.complex_damped_energy_antitone"
#check @MethbokeAddon.FDSN.complex_damped_energy_antitone
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.complex_damped_energy_antitone"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.complex_damped_energy_antitone"
#print axioms MethbokeAddon.FDSN.complex_damped_energy_antitone
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.complex_damped_energy_antitone"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.complex_damped_zero_on_Icc"
#check @MethbokeAddon.FDSN.complex_damped_zero_on_Icc
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.complex_damped_zero_on_Icc"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.complex_damped_zero_on_Icc"
#print axioms MethbokeAddon.FDSN.complex_damped_zero_on_Icc
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.complex_damped_zero_on_Icc"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.complex_work_le_normSq"
#check @MethbokeAddon.FDSN.complex_work_le_normSq
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.complex_work_le_normSq"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.complex_work_le_normSq"
#print axioms MethbokeAddon.FDSN.complex_work_le_normSq
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.complex_work_le_normSq"

#eval IO.println "TYPE_BEGIN:MethbokeAddon.FDSN.complex_forced_energy_bound"
#check @MethbokeAddon.FDSN.complex_forced_energy_bound
#eval IO.println "TYPE_END:MethbokeAddon.FDSN.complex_forced_energy_bound"
#eval IO.println "AXIOMS_BEGIN:MethbokeAddon.FDSN.complex_forced_energy_bound"
#print axioms MethbokeAddon.FDSN.complex_forced_energy_bound
#eval IO.println "AXIOMS_END:MethbokeAddon.FDSN.complex_forced_energy_bound"

