# Exact physical QFA target and complete zero-datum instance

**A-tier accepted at `ffbab0f5` / [run 44847013775](https://github.com/randogelist/Methboke/actions/runs/44847013775)** for the exact scoped declarations.
[Matching evidence](../../audits/material-ffbab0f5-qfa-accepted/independent-review.json). The general QFA root remains open.

This package fixes the current full-volume physical QFA proposition at
`8*norm(a)^4/(27*pi^4*nu^5)` and proves the complete conclusion for zero initial
data and positive viscosity. The strict-cutoff proposition and the stronger
closed-cutoff version are distinct. Pressure is explicitly fixed by the
smooth point gauge `p(t,0)=0`; no pressure Lp normalization is assumed.

The zero proof constructs full original Leray–Hopf nonemptiness. It then
handles every supplied zero-data path and every nonnegative tail start,
including zero: native smooth velocity and pressure, spatial a.e. agreement
at every tail time, exact energy equality with the original weak-gradient
witness, full shifted PDE membership, and uniqueness of L2 velocity against
every future from the exact own trace. Arbitrary time-null gradient values
are preserved; no pointwise gradient uniqueness is claimed.

All 29 public declarations passed independent literal consumers and named
type/transitive-axiom audits. Defining the all-data root is not a proof of that
root. The nonzero-data QFA construction remains open. No local Lean was run.

The mathematical chain is
`R3_NSE/QFA/DERIVATIONS/RESTART_HEAT_ZERO_CHAIN.txt`, sections 1 and 4.
