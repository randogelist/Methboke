import MethbokeAddon.FDSN.ResidualForce

/-!
# Locality and temporal support of the actual residual force

These statements use locality of the native totalized derivatives. They
remain valid without global regularity of the seed outside the time support
of the correction.
-/

set_option autoImplicit false

noncomputable section

open Set Filter SingularClosure
open MethbokeAddon.EhrenfestObstruction MethbokeAddon.FeffermanFamily
open scoped BigOperators ContDiff Topology

namespace MethbokeAddon.FDSN

theorem native_laplacian_zero : laplacian (0 : Field) = 0 := by
  funext x
  have hD (i : Fin 3) : coordinateDerivative (0 : Field) i = 0 := by
    funext y
    simp [coordinateDerivative]
  simp [laplacian, hD]

/-- A vanishing joint spacetime germ gives exact force agreement at the point.
No regularity of U beyond that germ is required. -/
theorem residualForce_eq_of_zero_germ
    (ν : ℝ) (U F h : Velocity) (t : ℝ) (x : Vec)
    (hh : (fun z : ℝ × Vec => h z.1 z.2) =ᶠ[𝓝 (t, x)] 0) :
    residualForce ν U F h t x = F t x := by
  have hx : h t x = 0 := hh.self_of_nhds
  have htime : timeDerivative h t x = 0 := by
    calc
      _ = timeDerivative (0 : Velocity) t x := nativeTimeDerivative_congr hh
      _ = 0 := by simp [timeDerivative]
  have hspace : fderiv ℝ (h t) x = 0 := by
    calc
      _ = fderiv ℝ ((0 : Velocity) t) x :=
        nativeSpatialFDeriv_congr (f := h) (g := (0 : Velocity)) (t := t) (x := x) hh
      _ = 0 := by simp
  have hlap : laplacian (h t) x = 0 := by
    calc
      _ = laplacian ((0 : Velocity) t) x :=
        nativeLaplacian_congr (u := h) (v := (0 : Velocity)) (t := t) (x := x) hh
      _ = 0 := congrFun native_laplacian_zero x
  have hUh : physicalTransport (U t) (h t) x = 0 := by
    simp [physicalTransport, hspace]
  have hhU : physicalTransport (h t) (U t) x = 0 := by
    simp [physicalTransport, hx]
  have hconv : convection (h t) x = 0 := by
    simp [convection, hspace]
  simp [residualForce, htime, hlap, hUh, hhU, hconv]

/-- Closed support of h as a time-to-field map controls every spacetime germ
outside it; no topology on the field codomain is used in this support. -/
theorem velocity_zero_germ_of_notMem_timeSupport
    (h : Velocity) {t : ℝ} (ht : t ∉ tsupport h) (x : Vec) :
    (fun z : ℝ × Vec => h z.1 z.2) =ᶠ[𝓝 (t, x)] 0 := by
  have hz : h =ᶠ[𝓝 t] 0 := notMem_tsupport_iff_eventuallyEq.mp ht
  have hz' : ∀ᶠ z : ℝ × Vec in 𝓝 (t, x), h z.1 = 0 :=
    (continuousAt_fst : ContinuousAt (fun z : ℝ × Vec => z.1) (t, x)).tendsto.eventually hz
  exact hz'.mono fun z hz => congrFun hz z.2

theorem residualForce_eq_of_notMem_timeSupport
    (ν : ℝ) (U F h : Velocity) {t : ℝ} (ht : t ∉ tsupport h) :
    residualForce ν U F h t = F t := by
  funext x
  exact residualForce_eq_of_zero_germ ν U F h t x
    (velocity_zero_germ_of_notMem_timeSupport h ht x)

/-- The complete native force correction has no larger temporal support than
the velocity correction, including all derivative and mixed transport terms. -/
theorem tsupport_residualForce_sub_subset
    (ν : ℝ) (U F h : Velocity) :
    tsupport (residualForce ν U F h - F) ⊆ tsupport h := by
  refine closure_minimal ?_ (isClosed_tsupport h)
  intro t ht
  by_contra hnot
  apply ht
  change residualForce ν U F h t - F t = 0
  rw [residualForce_eq_of_notMem_timeSupport ν U F h hnot, sub_self]

theorem hasCompactSupport_residualForce_sub
    (ν : ℝ) (U F h : Velocity) (hh : HasCompactSupport h) :
    HasCompactSupport (residualForce ν U F h - F) :=
  hh.isCompact.of_isClosed_subset (isClosed_tsupport _)
    (tsupport_residualForce_sub_subset ν U F h)

theorem residualForce_eq_off_time_interval
    (ν : ℝ) (U F h : Velocity) (a b : ℝ)
    (hh : tsupport h ⊆ Icc a b) {t : ℝ} (ht : t ∉ Icc a b) :
    residualForce ν U F h t = F t :=
  residualForce_eq_of_notMem_timeSupport ν U F h (fun hmem => ht (hh hmem))

/-- Positive compact time support of F and h yields positive compact time
support of the residual force. Smoothness and spatial periodicity are
independent admission clauses handled by subsequent actual-operator lemmas. -/
theorem residualForce_positive_time_support
    (ν : ℝ) (U F h : Velocity)
    (hF : ∃ a b : ℝ, 0 < a ∧ a < b ∧ ∀ t : ℝ, t ∉ Icc a b → F t = 0)
    (hh : ∃ a b : ℝ, 0 < a ∧ a < b ∧ tsupport h ⊆ Icc a b) :
    ∃ a b : ℝ, 0 < a ∧ a < b ∧
      ∀ t : ℝ, t ∉ Icc a b → residualForce ν U F h t = 0 := by
  obtain ⟨aF, bF, haF, habF, hFzero⟩ := hF
  obtain ⟨ah, bh, hah, habh, hhsupp⟩ := hh
  refine ⟨min aF ah, max bF bh, lt_min haF hah, ?_, ?_⟩
  · exact lt_of_le_of_lt (min_le_left _ _) (habF.trans_le (le_max_left _ _))
  · intro t ht
    have htF : t ∉ Icc aF bF := by
      intro hmem
      exact ht ⟨(min_le_left _ _).trans hmem.1, hmem.2.trans (le_max_left _ _)⟩
    have hth : t ∉ Icc ah bh := by
      intro hmem
      exact ht ⟨(min_le_right _ _).trans hmem.1, hmem.2.trans (le_max_right _ _)⟩
    rw [residualForce_eq_off_time_interval ν U F h ah bh hhsupp hth, hFzero t htF]

end MethbokeAddon.FDSN

