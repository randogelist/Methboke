# MLB18 — `MethbokeAddon.WeakFouriermanB.initial_front_physicalEnstrophy_hasDerivAt`

Actual physical NSE enstrophy derivative on its smooth front.

**Evidence:** `NAMED_EXTERNAL_TYPE_AXIOM_AUDIT_ACCEPTED` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import MethbokeAddon.WeakFouriermanB.PhysicalEnstrophyEvolution
```

[Raw cutout](../identities/MLB18.lean.txt) · [Full source context](../sources/S26_PhysicalEnstrophyEvolution.lean.txt) · [Pinned source, lines 314–323](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/PhysicalEnstrophyEvolution.lean#L314-L323)

```lean
theorem initial_front_physicalEnstrophy_hasDerivAt
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : InitialClassicalFront ν T a u p)
    (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) T) :
    HasDerivAt (fun r => physicalDissipation (u r)) (physicalEnstrophyRate ν (u t)) t := by
  have hu : ContDiffOn ℝ ∞ (fun z : ℝ × Vec => u z.1 z.2) (localFrontSpacetime T) :=
    H.velocity_smooth.mono (fun z hz => ⟨hz.1.le, hz.2⟩)
  have h := local_physicalDissipation_hasDerivAt u T hu
    (fun r hr => H.velocity_periodic r ⟨hr.1.le, hr.2⟩) t ht
  rwa [initial_front_enstrophy_pairing ν T a u p H t ht] at h
```

## Context and reuse boundary

This is actual-front calculus. It supplies no sign or lower growth bound.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `2335a18ccbb0ee6dda235abf5bc1b6bab4df2024`. Cutout SHA-256: `916fb80e781975e06e4a5561355241247ad0861cf5e3c5ff71e79ecd064341e2`.
