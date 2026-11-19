# AUX04 — `HasDerivWithinAt.mono`

Restrict the existing within-Ici derivative to the closed comparison slab.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import Mathlib.Analysis.Calculus.Deriv.Basic
```

[Raw cutout](../identities/AUX04.lean.txt) · [Full source context](../sources/S04_Basic.lean.txt) · [Pinned source, lines 373–375](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Deriv/Basic.lean#L373-L375)

```lean
theorem HasDerivWithinAt.mono (h : HasDerivWithinAt f f' t x) (hst : s ⊆ t) :
    HasDerivWithinAt f f' s x :=
  HasFDerivWithinAt.mono h hst
```

## Context and reuse boundary

Requires the actual set inclusion; it changes only the differentiation domain.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `99b298181811591362a2467cfd825017ac9d0fef`. Cutout SHA-256: `2728c09c94cc00fd55c89834545eea20bf8afdcfa1795a5a7e5175134f4262df`.
