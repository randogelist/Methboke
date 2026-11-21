# QFASixSectorL2

**Status: prepared; matching external cached compilation and exact named type/axiom audits required.**

This package constructs actual sector-restriction operators on `Lp (EuclideanSpace ℂ (Fin 3)) 2 volume` over all of Euclidean three-space. Each operator is built from the Borel sector indicator through `MemLp.indicator` and `MemLp.toLp`. Conjugation by Mathlib's L2 Fourier isometry gives actual complex-vector Fourier projections.

The 28 registered declarations comprise four definitions and 24 theorems. They establish norm contraction, complex linearity, continuous linear maps, idempotence, mutual annihilation, self-adjointness, orthogonality, exact reconstruction and squared-norm decomposition. A further a.e. theorem proves commutation with a scalar multiplier identity when both actual L2 representatives are supplied.

`Audit.lean` independently checks all complete public statements, the literal full-volume complex-vector carrier, actual indicator construction and actual Fourier conjugation. The package does not assume abstract projection operators, derivative witnesses beyond those stated, or a PDE solution.

The B-tier derivation is [SIX_SECTOR_L2_CHAIN.txt](../../R3_NSE/A-Regularity-class/DERIVATIONS/SIX_SECTOR_L2_CHAIN.txt). This advances the complex L2 part of P04. Preservation of the native real-valued range, weak-gradient/H1 and solenoidal commutation, physical gradient charges and NSE evolution remain open. Parent G05 is not closed by this package.

No local Lean, Lake, kernel audit or included runner was executed. Existing compiler, dependency and audit policies remain unchanged. Prepared code is not A-tier acceptance.
