import MethbokeAddon.WeakFouriermanB.AnalyticTwoSidedCap

/-!
The frozen data-class form of finite-cap analytic admission.

`D_Q` is the explicit zero union the nonzero smooth periodic solenoidal
mean-zero data admitting an actual two-sided analytic NSE pair through the
open horizon `2 * cutoff (criticalL2Representative a) nu`. The imported
`AnalyticTwoSidedNSECap` uses the ordinary time derivative throughout its
negative and positive time interval; it is distinct from the weaker
`AnalyticForwardNSECap` used internally by the finite-cap proof.

`R_nu` is the literal smooth-data class with an actual `GlobalSmoothNSE`
witness. Its existence statement occurs only in the target class. The
nonzero smooth datum assumption is retained from D_inf: it makes its physical
L2 representative nonzero, so the prescribed double-cutoff cap has the strict
overlap needed by the already prepared root. There is no cutoff positivity,
Serrin bound, trace identification or continuation premise hidden in D_Q.

For smooth data, `smooth_datum_cutoff` identifies the cutoff here with
`(physicalEnergy a)^2 / (8*pi^2*nu^5)`, the frozen tau_Q normalization.
The zero branch uses the existing explicit zero solution.

Prepared source only; external cached compiler/type/axiom evidence is pending.
No local Lean execution. This candidate is outside active Material discovery.
-/

set_option autoImplicit false

open Set MeasureTheory SingularClosure QuasiFeffermanB

namespace MethbokeAddon.WeakFouriermanB

noncomputable section

/-- The original target data class: smooth periodic solenoidal mean-zero
data with an actual globally smooth forward NSE solution. -/
def R_nu (ν : ℝ) : Set Field :=
  {a | SmoothSigmaZero a ∧
    ∃ (U : Velocity) (P : Pressure), GlobalSmoothNSE ν a U P}

/-- The frozen QFB admission class, including the explicit zero branch.
The nonzero branch uses a genuine two-sided analytic physical solution,
not a formal jet and not the weaker forward-only analytic predicate. -/
def D_Q (ν : ℝ) : Set Field :=
  {(0 : Field)} ∪ {a | SmoothSigmaZero a ∧ a ≠ 0 ∧
    ∃ (ε : ℝ) (u : Velocity) (p : Pressure), 0 < ε ∧
      AnalyticTwoSidedNSECap ν ε (2 * cutoff (criticalL2Representative a) ν) a u p}

/-- A continuous periodic nonzero datum cannot become the zero physical L2
class: almost-everywhere equality upgrades to pointwise equality through
the existing physical Fourier injectivity theorem. -/
theorem smooth_datum_representative_ne_zero
    {a : Field} (ha : SmoothSigmaZero a) (ha0 : a ≠ 0) :
    criticalL2Representative a ≠ 0 := by
  intro hzero
  have hrepzero : (criticalL2Representative a : Field)
      =ᵐ[volume.restrict unitCube] (0 : Field) := by
    rw [hzero]
    exact Lp.coeFn_zero Vec 2 (volume.restrict unitCube)
  apply ha0
  exact continuous_periodic_field_eq_of_cube_ae
    ha.smooth.continuous smoothSigmaZero_zero.smooth.continuous
    ha.periodic smoothSigmaZero_zero.periodic
    ((smooth_datum_representative_ae ha).symm.trans hrepzero)

/-- R0 in its frozen data-class form. Positive viscosity and membership of
the genuinely admitted class suffice. This theorem does not assert that
every analytic germ belongs to D_Q, nor that every smooth datum is admitted.
-/
theorem D_Q_subset_R_nu (ν : ℝ) (hν : 0 < ν) : D_Q ν ⊆ R_nu ν := by
  intro a ha
  rcases ha with hzero | ⟨hsmooth, hne, ε, u, p, hε, H⟩
  · obtain rfl := Set.mem_singleton_iff.mp hzero
    exact ⟨smoothSigmaZero_zero, 0, 0, globalSmoothNSE_zero ν⟩
  · have hcutoff : 0 < cutoff (criticalL2Representative a) ν :=
      CUTOFF_POS (criticalL2Representative a)
        (smooth_datum_representative_ne_zero hsmooth hne) hν
    obtain ⟨U, P, hglobal, hpreserve⟩ :=
      analytic_two_sided_cap_admission ν ε
        (2 * cutoff (criticalL2Representative a) ν) a u p hν hε
        (by linarith) H
    exact ⟨hsmooth, U, P, hglobal⟩

end

end MethbokeAddon.WeakFouriermanB
