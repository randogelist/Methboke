# R0AnalyticTwoSidedCap

`STATUS = PENDING_EXTERNAL_CI` · `NO_LOCAL_LEAN`

Literal two-sided analytic NSE cap uses the ordinary time derivative on the entire negative/positive interval. A proved derivative adapter gives the forward physical cap, and strict cutoff admission yields an actual global smooth pair preserving the forward cap.

The active proof source is byte-identical to the current candidate at
`PREPRINT_FORMALISATION/WeakFouriermanB/next/AnalyticTwoSidedCap.lean`. It is newly developed source, with a derivation basis at
`Material/_vendor/QuasiFeffermanB/RootContract.lean` in `67f766330918577e714e326be82eebfe29f5f2f7`. The basis is not a historical source-location claim;
`../owned-sources.json` separately records the current source hash.

All 5 public theorem signatures are independently stated in `Audit.lean`,
with complete fresh type and standard-axiom reports. The exact dependency
closure contains 271 source modules. External matching compilation and
audit evidence remain pending.

The analytic witness is an actual solution on its full two-sided open cap.
Its conversion to the physical forward derivative is proved, including at
time zero. The explicit admission premise remains; neither arbitrary-data
regularity nor universal analytic germ extension R1 is asserted.
