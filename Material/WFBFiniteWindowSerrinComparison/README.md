# WFBFiniteWindowSerrinComparison

`STATUS = PENDING_EXTERNAL_CI` · `NO_LOCAL_LEAN`

Physical finite-window Leray-Hopf/Serrin comparison from the same initial trace and a finite physical Serrin bound; the classical equation and pressure are required only on the comparison interval.

This newly developed owned source matches the current candidate at
`T3_NSE/B-Regularity-class/WFB/PREPRINT_FORMALISATION/next/FiniteWindowSerrinComparison.lean`. Its derivation basis is
`Material/_vendor/SingularClosure/CriticalSerrinUniqueness.lean` at `0402aa37ea09f90a216e63e5fe67c3f58bb2b844`.
That basis is not a claim that this new theorem source existed at that path
or revision. `../owned-sources.json` binds the current source hash separately.

`Audit.lean` independently states the full signatures of all 1 public
named theorem declarations and freshly emits their exact types and complete
axiom reports. Private proof helpers are included transitively in those reports.
The import closure contains 66 sources. No local compiler has run.

These finite-window lemmas support WFB-08. This package alone does not discharge
the entire obligation, local strong existence, maximal trajectory construction,
endpoint continuation or the global Weak_Fourierman_B root.
