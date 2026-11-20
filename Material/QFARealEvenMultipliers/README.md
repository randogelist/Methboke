# Actual real even bounded Fourier multipliers

The symbol record contains a real scalar function, measurability, evenness,
and a finite nonnegative pointwise norm bound. Native `MemLp.of_le_mul`
constructs frequency multiplication on actual complex L2 classes. The source
proves bounded complex linearity and exact commutation with the accepted
conjugate-reflection operator.

For real L2 input, the proved Hermitian range theorem identifies the inverse
Fourier output with an actual real field. The real operator and continuous
linear map retain the literal symbol `(m.value ξ : ℂ) • f ξ`, the original
full-volume carrier and the exact stated bound. Fourier injectivity proves
uniqueness. The two-way physical first-derivative bridge proves that applying
the multiplier to the supplied gradient gives the actual weak gradient of
the output, without differentiating the scalar symbol.

The package contains 24 public names: 19 theorems and five constructions,
with 33 independent audit consumers and ordered exact-type/axiom reports.
The audit expands the scalar record, actual L2 representative construction,
real inverse-Fourier construction and native compact smooth derivative tests.

The package is **prepared pending matching cached external verification**.
No local Lean, Lake, kernel or runner was executed. Accepted proof and
dependency bytes are unchanged.

This is reusable spatial infrastructure for the heat semigroup and H2
elliptic reconstruction. Those concrete symbols, strong continuity,
evolution laws and reconstruction conclusions require their own proofs.
No NSE existence or full finite-charge equivalence is claimed here.

Derivation: `R3_NSE/A-Regularity-class/DERIVATIONS/REAL_EVEN_MULTIPLIER_CHAIN.txt`.
