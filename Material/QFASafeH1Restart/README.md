# QFASafeH1Restart

This package is the first structured-assembly endpoint on
`codex/qfa-structured-assembly`.

It consumes the already accepted native supplied-path restart theorem and the
already accepted physical `H¹_σ(ℝ³)` graph.  It packages the selected trace
without changing either the velocity or the supplied weak-gradient witness.

The endpoint records one common witness containing:

- a time `s` with `0 < s < safeCutoff S ‖a‖ ν`;
- the exact datum `(u s, G s)` in `PhysicalH1Sigma`;
- the original energy start and restart data;
- full Leray--Hopf membership of the original translated path;
- the original strong right trace;
- the strict selected product bound.

It proves neither global weak existence nor a nonlinear strong solution,
continuation, weak--strong comparison, smoothness, sharp Sobolev admission, or
the final QFA root.

Status: `PENDING_MATCHING_EXTERNAL_CI`.  A mid-tier `!=!` signal is permitted
only after this exact source receives matching external compilation, all seven
fresh exact-type and theorem-level axiom reports, retained evidence,
publication, and terminal Material acceptance.
