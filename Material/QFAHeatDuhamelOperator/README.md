# Actual L2 forcing-to-continuous-response operator

**Status: A-tier accepted for the exact QFAHeatDuhamelOperator scope at `9b8250be`.**

[External run 44857358591](https://github.com/randogelist/Methboke/actions/runs/44857358591) passed the complete 534-module,
109-package, 1,435-report run, with fresh named audits, standalone QFB, complete
publication and the final gate. This package has 5 declarations
(4 theorems and 1 definitions) and 7 independent consumers.
[Exact independent review](../../audits/material-9b8250be-qfa-forced-heat-accepted/independent-review.json) ·
[New declaration index](../../audits/material-9b8250be-qfa-forced-heat-accepted/new-declaration-index.json).

This package constructs the actual bounded real linear map

$$
K_{\nu,T}:L^2((0,T];L^2(\mathbb R^3))
\longrightarrow C([0,T];L^2(\mathbb R^3))
$$

from the separately accepted `QFAHeatDuhamel` response. It uses the native
forcing `Lp SpatialL2 2 (volume.restrict (Ioc 0 T))` and the actual
`ContinuousMap (Icc 0 T) SpatialL2` carrier, with its supremum norm.
Every nonnegative viscosity and finite nonnegative horizon are covered,
including zero viscosity and `T = 0`.

Evaluation is the literal retarded physical heat integral

$$
(K_{\nu,T}F)(t)=\int_0^t S_\nu(t-s)F(s)\,ds.
$$

The preceding a.e. invariance theorem makes the construction respect the
forcing quotient. Its addition and real scalar-multiplication laws give
linearity. The actual continuity theorem supplies the continuous-path
codomain, and the proved uniform estimate gives

$$
\|K_{\nu,T}\|_{L^2\to C([0,T];L^2)}\le\sqrt T.
$$

Every output has exact zero initial trace. For any actual forcing function
`f` and its `MemLp 2` proof `hf`, evaluation on `hf.toLp f` equals the
original constructed response `duhamelL2 ν f t` at every `t ∈ [0,T]`.
This compatibility uses a.e. equality and does not equate arbitrary chosen
representatives pointwise.

## Exact verification surface

The package has **five public declarations: four theorems and one
definition**, with **seven independent consumers**. The namespace is
`MethbokeAddon.QuasiFeffermanA.HeatDuhamelOperator`.

| Public declaration | Exact scope |
|---|---|
| `duhamelL2Operator` | Actual continuous linear map from the forcing Lp quotient to continuous physical L2 paths. |
| `duhamelL2Operator_apply` | Evaluation as the literal retarded Bochner integral. |
| `duhamelL2Operator_norm_le` | Operator norm at most `Real.sqrt T`. |
| `duhamelL2Operator_zero_trace` | Exact zero initial trace for every forcing class. |
| `duhamelL2Operator_toLp_apply` | Compatibility with every admissible original forcing representative. |

The independent consumers also assemble one common operator with the
literal integral, zero trace and norm bound, and derive that the operator
on the zero-length horizon is exactly zero.

Every public declaration requires a named exact-type report and a
transitive axiom audit permitting only `propext`, `Classical.choice` and
`Quot.sound`. The operator is constructed from the actual response and its
proved properties; no continuity, linearity, norm-bound or response witness
is supplied as an additional hypothesis. The matching external evidence
above establishes only this exact package scope.

## Scope boundary

This is the continuous L2 response operator and its low-frequency bound.
Forced H1/H2 maximal regularity, the inhomogeneous derivative equation,
solenoidal response packaging and nonlinear local existence remain
subsequent constructions. The general QFA and WFA roots remain open.

The separate Duhamel package retains its own **15 declarations and 17
consumers**. This operator package adds **five declarations and seven
consumers**; their verification surfaces are distinct.

The next microscopic construction is the actual H2 heat semigroup with
the original H2 trace and strong continuity down to zero for regular forcing.
The inhomogeneous equation, forced energy estimate, density passage and
forced maximal regularity remain open.

[Source](../MethbokeAddon/QuasiFeffermanA/HeatDuhamelOperator.lean) ·
[Independent consumers](Audit.lean) ·
[Response package](../QFAHeatDuhamel/README.md) ·
[Derivation appendix](../../R3_NSE/QFA/DERIVATIONS/HEAT_DUHAMEL_CHAIN.txt)

No local Lean, Lake or kernel audit is executed.
