# AUX05 — `HasDerivWithinAt.hasDerivAt`

Turn a within-slab derivative into an ordinary derivative at an interior point.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
```

[Raw cutout](../identities/AUX05.lean.txt) · [Full source context](../sources/S04_Basic.lean.txt) · [Pinned source, lines 414–416](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L414-L416)

```lean
theorem HasDerivWithinAt.hasDerivAt (h : HasDerivWithinAt f f' s x) (hs : s ∈ 𝓝 x) :
    HasDerivAt f f' x :=
  HasFDerivWithinAt.hasFDerivAt h hs
```

## Context and reuse boundary

Requires the slab to be a neighborhood of that point; do not apply at its terminal boundary.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `99b298181811591362a2467cfd825017ac9d0fef`. Cutout SHA-256: `b5af57c3c0a579c6b0c143c35033315cdf54768181c8339dd2caf689888e9408`.
