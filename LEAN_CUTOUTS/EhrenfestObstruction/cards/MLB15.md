# MLB15 — `MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front`

Restricts a proposed global smooth NSE pair to any finite physical front.

**Evidence:** `NAMED_EXTERNAL_TYPE_AXIOM_AUDIT_ACCEPTED` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import MethbokeAddon.WeakFouriermanB.LocalClassicalUniqueness
```

[Raw cutout](../identities/MLB15.lean.txt) · [Full source context](../sources/S23_LocalClassicalUniqueness.lean.txt) · [Pinned source, lines 48–61](https://github.com/randogelist/Methboke/blob/fdb515d8bde35ec8021bbc26f360aca8dfa2855c/Material/MethbokeAddon/WeakFouriermanB/LocalClassicalUniqueness.lean#L48-L61)

```lean
theorem global_smooth_to_initial_front
    (ν T : ℝ) (a : Field) (u : Velocity) (p : Pressure)
    (H : GlobalSmoothNSE ν a u p) : InitialClassicalFront ν T a u p := by
  exact {
    velocity_smooth := H.velocity_smooth.mono (fun _ hz => hz.1)
    pressure_smooth := H.pressure_smooth.mono (fun _ hz => hz.1)
    velocity_periodic := fun t ht => H.velocity_periodic t ht.1
    pressure_periodic := fun t ht => H.pressure_periodic t ht.1
    divergence_free := fun t ht => H.divergence_free t ht.1
    equation := fun t ht => H.equation t ht.1
    initial := H.initial
    velocity_mean_zero := fun t ht => H.velocity_mean_zero t ht.1
    pressure_mean_zero := fun t ht => H.pressure_mean_zero t ht.1
  }
```

## Context and reuse boundary

Does not compare that front with spectral approximations.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

**Native source context:**

```lean
set_option autoImplicit false
open Set Filter MeasureTheory SingularClosure
open scoped ContDiff Topology
namespace MethbokeAddon.WeakFouriermanB
noncomputable section
```

Only restricts the supplied physical solution; no Galerkin stability or approximation conclusion.

Earlier helpers noted by source review (not an exhaustive dependency list): `InitialClassicalFront`, `initialFrontSpacetime`.

Source blob: `bfe2ae01851909b2e95e343867e55f19b74f1b71`. Cutout SHA-256: `831b2210a7e9a63009a88565a6d0d97048b64416f3d2761fe9a71c4ab07be349`.
