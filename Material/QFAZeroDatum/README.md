# Exact physical QFA target and complete zero-datum instance

This package fixes the current full-volume physical QFA proposition at
`8*norm(a)^4/(27*pi^4*nu^5)` and prepares a complete proof for zero initial
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

**Status: prepared pending matching external verification.** All 29 public
declarations have independent literal consumers and named type/transitive-
axiom audit requirements. Defining the all-data root is not a proof of that
root. The nonzero-data QFA construction remains open. No local Lean was run.

The mathematical chain is
`R3_NSE/QFA/DERIVATIONS/RESTART_HEAT_ZERO_CHAIN.txt`, sections 1 and 4.
