# QFA: whole-space native integration

Status: **compiler-guided repair prepared, pending matching cached external verification**.

This is the scoped `AC-Integration` development within Methboke. The retained
main program remains Fefferman D. The [integration record](INTEGRATION_STATUS.json)
separates source preparation, exact external evidence and the open physical root.

## Integrated source layers

| Layer | Native location | Exact scope |
|---|---|---|
| Recovered QFA | `Material/_vendor/QFA/` and `QFA.lean` | 108 historical named energy, representation, trace, comparison and conditional-assembly declarations, with unchanged hypotheses and constants |
| Compact tests and spectral reduction | `Material/_vendor/QFALC004/`, `QFALC005/`, `QFALC001Reduction/` | Density and compact-Schwartz extension; Fourier multiplier identities and exact spectral reduction |
| Conditional historical root | `Material/_vendor/QFACorrectedRoot/` | Historical QFA implication with explicit class realization, comparison, analytic and smoothness assumptions |
| Owned Fourier multiplier port | `Material/MethbokeAddon/QuasiFeffermanA/FourierMultipliers.lean` | Five corrected derivative-witness multiplier proofs under an owned namespace; original failed upstream source preserved inactive |
| Native spectral realization | `Material/MethbokeAddon/QuasiFeffermanA/Spectral.lean` | Derives the two Fourier norm densities and inhabits WholeSpaceSpectralEndpoint from actual Schwartz derivative witnesses |
| Physical contracts | `Material/MethbokeAddon/QuasiFeffermanA/Contracts.lean` | Full-volume R3 L2; all compact scalar tests; actual weak derivatives and solenoidal momentum tests; standard LH energy-class fields |
| Energy and traces | `Material/MethbokeAddon/QuasiFeffermanA/Energy.lean` | Weighted budget, initial energy bound, strong initial/right traces, energy restart data and zero-datum velocity rigidity |
| Safe cutoff | `Material/MethbokeAddon/QuasiFeffermanA/Cutoff.lean` | Positive scalar threshold, half-budget identity, strict good time and half-measure bound |
| Physical energy-class selection | `Material/MethbokeAddon/QuasiFeffermanA/Integration.lean` | Actual solenoidal weak-gradient energy start strictly before the safe cutoff, with a derived strong right trace |

The new sources are audited through `QFANativeFoundation`. The recovered
sources use `QFARecovered`, `QFARepresentation` and `QFAConditionalRoot`.
All source identities are registered in the existing native manifests.
The four new audit packages request 188 named reports: 129 recovered results,
five historical root/assumption contracts, and 54 new native declarations
(35 public helper theorems plus 19 contracts/definitions).
[Static validation](STATIC_VALIDATION.json) checks bytes and metadata only.

## Exact finite-window conclusion

For a supplied whole-space LH path, set

$$E(t)=\|u(t)\|_2^2,\qquad Y(t)=\sum_{j=1}^3\|G_j(t)\|_2^2,\qquad M=\|a\|_2.$$

For every finite positive horizon, the native energy adapter gives a genuinely
integrable product and the weighted budget

$$\int_0^R E(t)Y(t)\,dt\le\frac{M^4}{4\nu}.$$

For any scalar $S>0$ and $\nu>0$, define

$$\theta=\frac{\nu^4}{S^6},\qquad
\tau=\frac{S^6M^4}{2\nu^5}.$$

Then $M^4/(4\nu)=\theta\tau/2$. For nonzero datum the prepared endpoint
selects $0<s<\tau$ with an actual weak-gradient solenoidal trace, an admissible
energy start, translated energy/trace data, strong right convergence at $s$
and $E(s)Y(s)<\theta$. The set retaining these properties and strict product
smallness has measure at least $\tau/2$.

The numerical identity $S^6=16/(27\pi^4)$ rewrites $\tau$ to
$8M^4/(27\pi^4\nu^5)$ **only under that explicit scalar hypothesis**.
A sharp Sobolev inequality is a separate analytic obligation. For zero datum,
$\tau=0$ and the supplied LH velocity vanishes at every nonnegative time;
no positive restart is selected from an empty interval.

## What is still required for the complete QFA theorem

The concrete contract has no existence, continuation, smoothness, comparison
or QFA field. Those results must be constructed. In particular, the remaining
work includes global LH nonemptiness for every original L2-sigma datum,
H1 strong local theory and continuation, spatial estimates with admissible
constants, physical weak-strong comparison, full shifted LH membership,
closed smooth tails with pressure and energy equality, and future uniqueness
from each path's own tail trace.

The historical corrected root remains an implication with explicit analytic
inputs and a different historical cutoff. Accepting that implication does not
supply those inputs or establish the current physical QFA statement.
Periodic QFB remains a separately accepted reference. WFA is a follow-on.

## First external attempt and repair

[Run44782428295](https://github.com/randogelist/Methboke/actions/runs/44782428295)
at73501cde reused all420prior modules and compiled37new modules. It found two
proof elaboration errors in Cutoff and compiler failures in the previously
unaudited recovered DistributionMultipliers file. No new result was accepted
and no passed cache was published. [Exact failure evidence](../../audits/material-73501cde-qfa-failed/summary.json) is retained.

The cutoff repair keeps all public statement types unchanged. The original
multiplier file and its barrel remain byte-identical but are outside active
imports; the corrected five-proof port belongs to an explicitly owned namespace.
Its proofs feed the native Spectral module and receive fresh named audits.

## Verification boundary

Only authorized external cached compilation and fresh exact-type/axiom audits
can accept this source. Independent consumers expand the physical contracts
and theorem signatures, and the audit prints every required full type and axiom
set. No local Lean, Lake, kernel audit or archived runner is executed.

The Material workflow only gains the `AC-Integration` push branch. Compiler,
Mathlib, lockfile, lakefile, drivers, cache policy and axiom rules are unchanged.
The complete final result and evidence identifiers will be recorded here after
inspection; source preparation is not A-tier acceptance.
