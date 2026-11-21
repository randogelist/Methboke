# QFAPhysicalH1SigmaSectors

**Status: prepared; matching cached external compilation and complete named type/axiom audits are required.**

The package constructs the six Fourier projections on the native closed `PhysicalH1Sigma` graph. Solenoidal preservation is proved before constructing the projected graph elements: the actual coordinate slices commute with the real sector operator, so the trace of the projected weak gradients is the projection of the original trace. The independent compact-test divergence criterion then gives native solenoidality.

The two source roots contain 32 registered declarations: four definitions and 28 theorems. Ten names belong to the codomain/coordinate naturality layer, and 22 belong to the native solenoidal H1 construction.

`SixSectorNaturality.lean` proves complex codomain naturality of the actual L2 Fourier transform using the integrable Schwartz formula, continuity and native Schwartz density. Literal scalar indicators commute with the same bounded complex-linear maps. Injective componentwise complexification transfers this result to the actual real coordinate slices used by the physical trace. No generic projector, Fourier commutation or solenoidal-preservation premise is assumed.

`PhysicalH1SigmaSectors.lean` constructs an actual real-linear isometric inclusion into full `PhysicalH1` and the projected native solenoidal graph element. It proves real linearity, norm contraction, continuous linear packaging, idempotence, mutual annihilation, reconstruction, self-adjointness, orthogonality and exact H1 squared-norm splitting. Its final identities expose the actual weak-gradient charge sum and the literal cone-restricted Fourier integral with factor `4 * Real.pi ^ 2` on the original solenoidal carrier.

`Audit.lean` independently consumes all complete public signatures from both source roots. It expands the full-volume vector carriers, compact-test weak-gradient and solenoidal predicates, coordinate-slice construction, native closed graph, isometric inclusion, projected graph elements and physical charge formulas. Ordered named type and axiom reports retain the existing standard-axiom policy.

The B-tier derivation is [SOLENOIDAL_H1_SECTORS_CHAIN.txt](../../R3_NSE/A-Regularity-class/DERIVATIONS/SOLENOIDAL_H1_SECTORS_CHAIN.txt), with the independent divergence proof in [PHYSICAL_H1_DIVERGENCE_CHAIN.txt](../../R3_NSE/A-Regularity-class/DERIVATIONS/PHYSICAL_H1_DIVERGENCE_CHAIN.txt). Matching external evidence is required for every new upstream source and this package before any A-tier scope change.

No physical NSE evolution, local or maximal solution construction, continuation, sharp spatial estimate, universal time-budget finiteness or physical class root follows from this scoped package. No local Lean, Lake, kernel audit or runner was executed, and accepted source bytes, dependency pins and audit policies remain unchanged.
