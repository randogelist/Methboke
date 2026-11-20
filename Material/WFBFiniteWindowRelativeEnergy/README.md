# WFBFiniteWindowRelativeEnergy

`STATUS = PENDING_EXTERNAL_CI` · `NO_LOCAL_LEAN`

Derived physical classical energy equality and weak/classical RAW and TRANSPORT relative-energy inequalities with NSE and pressure premises restricted to a finite compact interval.

This newly developed owned source matches the current candidate at
`T3_NSE/B-Regularity-class/WFB/PREPRINT_FORMALISATION/next/FiniteWindowRelativeEnergy.lean`. Its derivation basis is
`Material/_vendor/SingularClosure/CriticalRelativeEnergyTransport.lean` at `0402aa37ea09f90a216e63e5fe67c3f58bb2b844`.
That basis is not a claim that this new theorem source existed at that path
or revision. `../owned-sources.json` binds the current source hash separately.

`Audit.lean` independently states the full signatures of all 3 public
named theorem declarations and freshly emits their exact types and complete
axiom reports. Private proof helpers are included transitively in those reports.
The import closure contains 55 sources. No local compiler has run.

These finite-window lemmas support WFB-08. This package alone does not discharge
the entire obligation, local strong existence, maximal trajectory construction,
endpoint continuation or the global Weak_Fourierman_B root.
