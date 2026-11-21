# QFAACBudget

**Prepared; matching external acceptance is pending.**

Scalar AC-to-Volterra comparison, integral Gronwall and uniform bound from an explicitly finite full stopped square budget.

This package advances G03, plan P15. Its exact public signatures and literal carrier/budget checks are in [Audit.lean](Audit.lean); every named declaration receives a fresh type and axiom report. The allowed axioms remain `propext`, `Classical.choice`, and `Quot.sound`.

The prior B-tier derivation is [recorded here](../../R3_NSE/A-Regularity-class/DERIVATIONS/AC_BUDGET_CHAIN.txt). The six parent targets and actual PDE obligations remain explicit. This scoped package does not prove a full QFA/WFA root, universal budget finiteness, sharp spatial admission, or actual R3 NSE existence.

Compiler and dependencies retain the existing native pin. No local Lean, Lake, kernel audit or runner was executed.
