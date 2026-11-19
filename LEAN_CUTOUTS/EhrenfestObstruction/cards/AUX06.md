# AUX06 — `HasDerivWithinAt.continuousWithinAt`

Obtain within-domain continuity from the actual derivative, including one-sided endpoints.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
```

[Raw cutout](../identities/AUX06.lean.txt) · [Full source context](../sources/S04_Basic.lean.txt) · [Pinned source, lines 847–849](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L847-L849)

```lean
theorem HasDerivWithinAt.continuousWithinAt (h : HasDerivWithinAt f f' s x) :
    ContinuousWithinAt f s x :=
  HasDerivAtFilter.tendsto_nhds inf_le_left h
```

## Context and reuse boundary

No two-sided initial-time smoothness follows from this theorem.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `99b298181811591362a2467cfd825017ac9d0fef`. Cutout SHA-256: `0ca7e0682da0aad850c7962d959e0d189db85c28e991c1f676bfd4adb6b7621a`.
