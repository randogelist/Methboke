# QFAPhysicalH1Sectors

**Status: prepared; matching cached external compilation and complete named type/axiom audits are required.**

The source constructs the six Fourier projections on the actual full-space real `PhysicalH1` carrier. Each projected element contains the projected L2 velocity and the projections of its three supplied weak gradients. The two-way compact-test Fourier theorem proves that these fields are the actual weak derivatives of the projected velocity. No H2 or Laplacian witness is required.

The 34 declarations comprise three definitions and 31 theorems. They establish derivative commutation, real linearity, norm contraction, continuous linear operators, idempotence, mutual annihilation, reconstruction, self-adjointness, orthogonality and exact inhomogeneous H1 norm splitting. The actual squared-gradient charges are nonnegative, continuous and exactly additive. Their literal sector Fourier integrals retain the factor `4 * Real.pi ^ 2`, with genuine weighted integrability obtained from the physical first derivatives. The explicit pointwise factor-six inequality is included.

The final four theorems specialize the accepted factor-six comparisons to the constructed physical charges. They use full stopped windows and extended nonnegative integrals, preserving infinite values. Continuity on the open lifetime gives the exact sum of the six individual budgets and their finiteness equivalence. This supplies no continuation through a finite maximal endpoint and makes no universal budget-finiteness claim.

`Audit.lean` independently consumes every full public signature and expands the full-volume carriers, compact-test graph predicate, projected graph elements, physical charges and stopped-budget definitions. Its ordered named type and axiom reports retain the existing standard-axiom policy.

The B-tier construction is [PHYSICAL_H1_SECTORS_NATIVE_CHAIN.txt](../../R3_NSE/A-Regularity-class/DERIVATIONS/PHYSICAL_H1_SECTORS_NATIVE_CHAIN.txt), refining [REAL_H1_SECTOR_LIFT_CHAIN.txt](../../R3_NSE/A-Regularity-class/DERIVATIONS/REAL_H1_SECTOR_LIFT_CHAIN.txt). The upstream real L2 transport and H1 spectral identities are separate new source packages and require their own matching evidence.

The source acts on full `PhysicalH1`. Its restriction to the native solenoidal subspace still requires the compact-test divergence criterion and scalar-multiplier compatibility. This package does not assume that missing result or close parent G05. Native NSE existence, continuation, physical time evolution, sharp spatial admission and the physical class root remain separate obligations.

No local Lean, Lake, kernel audit or included runner was executed. Accepted source bytes, dependency pins and audit policies are preserved.
