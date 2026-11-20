# AUX03 — `HasDerivWithinAt.norm_sq`

Differentiate a real Hilbert norm square within an interval.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import Mathlib.Analysis.InnerProductSpace.Calculus
```

[Raw cutout](../identities/AUX03.lean.txt) · [Full source context](../sources/S10_Calculus.lean.txt) · [Pinned source, lines 223–226](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/InnerProductSpace/Calculus.lean#L223-L226)

```lean
theorem HasDerivWithinAt.norm_sq {f : ℝ → F} {f' : F} {s : Set ℝ} {x : ℝ}
    (hf : HasDerivWithinAt f f' s x) :
    HasDerivWithinAt (‖f ·‖ ^ 2) (2 * ⟪f x, f'⟫) s x := by
  simpa using hf.hasFDerivWithinAt.norm_sq.hasDerivWithinAt
```

## Context and reuse boundary

Does not supply the forced-error derivative or a general Sobolev-valued evolution.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `0cb732b074509d4aa9fccd3c3f83d30f9021eb90`. Cutout SHA-256: `a8557db2cfc07f23f5cf9ea26d7b7b71e1ba4371f8a569cc2ebb28c48e3229e9`.
