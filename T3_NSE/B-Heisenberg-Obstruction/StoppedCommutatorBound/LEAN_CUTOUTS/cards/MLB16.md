# MLB16 — `MethbokeAddon.WeakFouriermanB.initial_classical_front_unique`

Physical smooth-front uniqueness for same datum, including normalized pressure.

**Evidence:** `NAMED_EXTERNAL_TYPE_AXIOM_AUDIT_ACCEPTED` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import MethbokeAddon.WeakFouriermanB.LocalClassicalUniqueness
```

[Raw cutout](../identities/MLB16.lean.txt) · [Full source context](../sources/S23_LocalClassicalUniqueness.lean.txt) · [Pinned source, lines 135–186](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/LocalClassicalUniqueness.lean#L135-L186)

```lean
theorem initial_classical_front_unique
    (ν T S : ℝ) (a : Field) (u v : Velocity) (p q : Pressure)
    (hν : 0 < ν) (hT : 0 < T) (hS : 0 < S)
    (H : InitialClassicalFront ν T a u p)
    (K : InitialClassicalFront ν S a v q) :
    ∀ r ∈ Ico (0 : ℝ) (min T S), u r = v r ∧ p r = q r := by
  have ha := initial_front_initial_smooth ν T a u p H hT
  obtain ⟨w, G, hw, _⟩ := smooth_datum_lerayHopf_exists ν hν a ha
  have hwu := initial_front_leray_hopf_identification ν T a u p w G H hν hT hw
  have hwv := initial_front_leray_hopf_identification ν S a v q w G K hν hS hw
  have htimeT (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (min T S)) :
      r ∈ Ico (0 : ℝ) T := ⟨hr.1.le, hr.2.trans_le (min_le_left T S)⟩
  have htimeS (r : ℝ) (hr : r ∈ Ioo (0 : ℝ) (min T S)) :
      r ∈ Ico (0 : ℝ) S := ⟨hr.1.le, hr.2.trans_le (min_le_right T S)⟩
  have huv : ∀ r ∈ Ioo (0 : ℝ) (min T S), u r = v r := by
    intro r hr
    exact continuous_periodic_field_eq_of_cube_ae
      (initial_front_smooth_slices ν T a u p H r (htimeT r hr)).smooth.continuous
      (initial_front_smooth_slices ν S a v q K r (htimeS r hr)).smooth.continuous
      (H.velocity_periodic r (htimeT r hr)) (K.velocity_periodic r (htimeS r hr))
      ((hwu r ⟨hr.1, (htimeT r hr).2⟩).symm.trans
        (hwv r ⟨hr.1, (htimeS r hr).2⟩))
  have hpq : ∀ r ∈ Ioo (0 : ℝ) (min T S), p r = q r := by
    apply normalized_pressure_eq_on_jointly_smooth_velocity_overlap isOpen_Ioo huv
    · intro r hr
      exact H.equation r (htimeT r hr)
    · intro r hr
      exact K.equation r (htimeS r hr)
    · exact H.pressure_smooth.mono (fun z hz => htimeT z.1 hz)
    · exact K.pressure_smooth.mono (fun z hz => htimeS z.1 hz)
    · intro r hr
      exact H.pressure_mean_zero r (htimeT r hr)
    · intro r hr
      exact K.pressure_mean_zero r (htimeS r hr)
  have hpq0 : p 0 = q 0 := by
    funext x
    apply continuousOn_Ico_eq_at_zero (lt_min hT hS)
      (f := fun r => p r x) (g := fun r => q r x)
    · exact H.pressure_smooth.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr.1, hr.2.trans_le (min_le_left T S)⟩)
    · exact K.pressure_smooth.continuousOn.comp
        (continuous_id.prodMk continuous_const).continuousOn
        (fun r hr => ⟨hr.1, hr.2.trans_le (min_le_right T S)⟩)
    · intro r hr
      exact congrFun (hpq r hr) x
  intro r hr
  rcases eq_or_lt_of_le hr.1 with hzero | hpos
  · have hrzero : r = 0 := hzero.symm
    subst r
    exact ⟨H.initial.trans K.initial.symm, hpq0⟩
  · exact ⟨huv r ⟨hpos, hr.2⟩, hpq r ⟨hpos, hr.2⟩⟩
```

## Context and reuse boundary

Supports identifying an independently constructed limit; no Galerkin convergence follows from uniqueness alone.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `bfe2ae01851909b2e95e343867e55f19b74f1b71`. Cutout SHA-256: `dbac8fb16d57b6d3621317ff2b58952b9c4c368c10303769cf60c6bda0169100`.
