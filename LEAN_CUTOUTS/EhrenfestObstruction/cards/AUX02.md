# AUX02 — `HasDerivWithinAt.inv`

Differentiate the reciprocal on Ici 0 directly, including the initial endpoint.

**Evidence:** `SOURCE_ONLY_PINNED_REVISION_READ` for the original declaration. This extracted reference has not been compiled or newly audited.

**Reuse through the original module:**

```lean
import Mathlib.Analysis.Calculus.Deriv.Inv
```

[Raw cutout](../identities/AUX02.lean.txt) · [Full source context](../sources/S06_Inv.lean.txt) · [Pinned source, lines 104–108](https://github.com/leanprover-community/mathlib4/blob/db584cd6d46c92f209a44c0f1c829460d327499d/Mathlib/Analysis/Calculus/Deriv/Inv.lean#L104-L108)

```lean
@[to_fun]
theorem HasDerivWithinAt.inv (hc : HasDerivWithinAt c c' s x) (hx : c x ≠ 0) :
    HasDerivWithinAt (c⁻¹) (-c' / c x ^ 2) s x := by
  convert! (hasDerivAt_inv hx).comp_hasDerivWithinAt x hc using 1
  ring
```

## Context and reuse boundary

Requires a nonzero denominator. The NSE derivative identity and positivity must be supplied.

The excerpt retains its original source spelling. Section parameters, namespace openings, local instances and earlier helpers may be outside this excerpt. Import the original module to use the existing declaration. Copying the excerpt into a fresh file is not a standalone proof package, and importing its defining module and then redeclaring the same name creates a duplicate declaration.

Source blob: `9872e356f606bd1be308cc10127da3c716f7a6f8`. Cutout SHA-256: `69f33574c5ed2d33d4f1644e9f40f20712679f599f719b268277f6f38303a464`.
