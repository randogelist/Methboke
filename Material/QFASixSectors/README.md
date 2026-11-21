# QFASixSectors

**Status: prepared; matching external cached compilation and exact named type/axiom audits required.**

This package constructs the six registered even Borel cones on the actual Euclidean three-space, ordered by the permutations `012, 021, 102, 120, 201, 210`. Decreasing absolute coordinate magnitude determines the order; lower coordinate indices win ties. The origin belongs exactly to sector 0.

It proves measurability, exact disjointness, unique membership, exhaustion, antipodal symmetry and nonempty interiors. The literal real indicator symbols are measurable, bounded by one, even, idempotent, pairwise orthogonal and sum to one pointwise. All boundary points are included exactly once.

The 17 audited public declarations comprise two definitions and fifteen theorems. `Audit.lean` independently consumes every complete statement and expands the literal spatial carrier, six inequalities and indicators. No abstract partition or multiplier premises replace the actual construction.

The B-tier derivation is [SIX_SECTORS_CHAIN.txt](../../R3_NSE/A-Regularity-class/DERIVATIONS/SIX_SECTORS_CHAIN.txt). This is the P03 part of G05. The package does not construct physical Fourier projections, real inverse-Fourier range, H1/solenoidal commutation, charge additivity or an NSE solution. G05 and the NSE-A root remain open.

No local Lean, Lake, kernel audit or included runner was executed. Compiler, dependency and audit policies are retained; preparation alone gives no A-tier acceptance.
