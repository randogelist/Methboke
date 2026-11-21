# QFA stopped windows and complete nonnegative budgets

This package stops an arbitrary `ENNReal` lifetime by a finite real cutoff,
proves that the minimum is finite, and only then uses its real endpoint.
The original observation set is exactly the resulting open interval. Zero
lifetimes, zero cutoffs and infinite lifetimes are covered.

Full nonnegative budgets equal the supremum of all partial budgets and the
literal limit from below, including infinite values. Finiteness is equivalent
to one common finite bound on the partial budgets. The construction needs no
measurability assumption for these directed-union statements. Ordinary
integral bridges retain genuine integrability or continuity on the particular
compact partial interval; no terminal continuity is inferred.

There are **63 public declarations: 57 theorems and 6 definitions**, split
between `StoppedWindow.lean` and `FullStoppedBudget.lean`. The independent audit
consumes every complete signature and includes literal expansions of the
stopped window, budget, left limit and uniform-bound contract.

The source is **prepared pending matching cached external verification**.
Only standard axioms are allowed. No local Lean, Lake, kernel or audit runner
has been executed.

This is the stopping and generic integration part of P08/G06. Actual physical
Fourier/gauge instantiation is a separate layer. Construction of a canonical
NSE solution and its finite-budget/globality equivalence remain separate
analytical obligations.

Derivation: `R3_NSE/A-Regularity-class/DERIVATIONS/FULL_STOPPED_WINDOW_GAUGE_CHAIN.txt`.
