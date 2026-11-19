# WFBFiniteFrontTest

`STATUS = PENDING_EXTERNAL_CI` · `NO_LOCAL_LEAN`

Actual finite physical NSE front supplies global positive smooth solenoidal weak-momentum tests agreeing through shorter horizons and near zero. The test is not asserted to solve NSE outside the finite front.

This newly developed owned source matches the current candidate at
`PREPRINT_FORMALISATION/WeakFouriermanB/next/FiniteFrontTest.lean`. Its derivation basis is
`Material/MethbokeAddon/WeakFouriermanB/LocalFront.lean` at `0402aa37ea09f90a216e63e5fe67c3f58bb2b844`.
That basis is not a claim that this new theorem source existed at that path
or revision. `../owned-sources.json` binds the current source hash separately.

`Audit.lean` independently states the full signatures of all 5 public
named theorem declarations and freshly emits their exact types and complete
axiom reports. Private proof helpers are included transitively in those reports.
The import closure contains 176 sources. No local compiler has run.

These finite-window lemmas support WFB-08. This package alone does not discharge
the entire obligation, local strong existence, maximal trajectory construction,
endpoint continuation or the global Weak_Fourierman_B root.
