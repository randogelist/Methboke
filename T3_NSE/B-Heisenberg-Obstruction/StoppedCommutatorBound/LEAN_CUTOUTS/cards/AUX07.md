# AUX07 — `HasDerivWithinAt.continuousOn`

Package pointwise within derivatives into continuity on the closed slab.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
```

[Raw cutout](../identities/AUX07.lean.txt) · [Full source context](../sources/S04_Basic.lean.txt) · [Pinned source, lines 854–855](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L854-L855)

```lean
theorem HasDerivWithinAt.continuousOn {f f' : 𝕜 → F} (h : ∀ x ∈ s, HasDerivWithinAt f (f' x) s x) :
    ContinuousOn f s := fun x hx => (h x hx).continuousWithinAt
```

## Context and reuse boundary

The derivative hypotheses must hold at every point of the stated set.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `99b298181811591362a2467cfd825017ac9d0fef`. Cutout SHA-256: `a3feceb9b73ec5e894915add7b90ea90c9001bf2a875db49d23e8d6ff5bf7c11`.
