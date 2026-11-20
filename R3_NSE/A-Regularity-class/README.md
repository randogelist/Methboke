# NSE-A regularity class: finite six-charge budget

## External compilation repair

[Run 44832766266](https://github.com/randogelist/Methboke/actions/runs/44832766266) at source `4c15c473` passed
510 of 512 scheduled modules. There were
1 new-source failures and 1 blocked dependents.
The exact original evidence is retained in [audits/material-4c15c473-nse-a-failed](../../audits/material-4c15c473-nse-a-failed/summary.json).

Candidate repair: Qualify the scalar-action-on-zero simplifier and reduce the literal True branch in the final LeraySolenoidal coordinate proof. H2Spectral and its endpoint now compile.

Public statements and independent consumers are preserved. All 99 fresh
package audits, 1,294 named reports, publication and final acceptance remain
required. The last accepted source remains `09bcf251`; no new acceptance is
claimed from a partial run.

## Current candidate: H2, Leray and real multipliers

The next external candidate adds **202 declarations** in four packages:
the actual closed H2 graph and its exact Hessian–Laplacian norm identity;
the constructed real Leray projection and its native L2/H1 solenoidal range;
bounded real even Fourier multipliers with actual weak-gradient transport;
and the exact real L2/H1 heat semigroup with contraction and strong continuity.
It also repairs the missing `NNReal` notation scope exposed by
[the first stopped-budget run](https://github.com/randogelist/Methboke/actions/runs/44824925503).
The combined candidate requires **512 modules, 99 fresh package audits and
1294 named reports**. The 307 additions across these two batches are pending
matching external verification. The full canonical NSE-A theorem remains open.


## Active construction: full stopped budgets and gauge

The selected scoped goal is **`NSE_A_FINITE_CHARGE_IFF_GLOBAL`**. The next
candidate adds **105 declarations: 91 theorems and 14 definitions**, in
`QFAStoppedBudget` and `QFAPhysicalStoppedGauge`. It supplies the actual finite
observation window, complete endpoint budget limits including infinity,
physical/Fourier normalization, fourth-root gauge and integer sublevels.
These additions are **prepared pending matching external verification**.
The new registry contains 95 packages and 1092 named reports; the previously
accepted G05/P01–P07 proof and audit bytes are preserved.

The native H2, real Leray, local solution, sharp spatial estimate, evolution,
continuation and literal solution-category layers remain separate obligations.
The canonical class theorem and universal budget finiteness remain open.


## Current native construction

**G05 and P01–P07 are A-tier accepted at `09bcf251`**, [external run 44820225574](https://github.com/randogelist/Methboke/actions/runs/44820225574). All **496 modules, 93 fresh package audits and 987 named type/axiom reports** passed. The latest seven packages add **134 declarations: 116 theorems and 18 definitions**. Only standard axioms occur; publication and final acceptance passed. The original G05 physical H1/Fourier/six-projector scope is complete. G01, G02, G03, G04 and G06, the canonical NSE-A class root and universal budget finiteness remain open. No local Lean was executed.

[Six targets](SIX_GAP_A_TIER_TARGETS.txt) · [Accepted scopes and names](SIX_GAP_A_TIER_ACCEPTED_HELPERS.txt) · [Current implementation status](SIX_GAP_IMPLEMENTATION_STATUS.json)

**Status: B-tier analytic class equivalence.** This page registers a class of
whole-space initial data through the finite budget of their canonical maximal
strong solutions. The [complete cumulative derivation](NSE_A_FINITE_CHARGE_CLASS_B_TIER.txt)
contains the hypotheses, proofs, endpoint conventions and source register.
The [machine-readable status](STATUS.json) records this registration separately
from the accepted QFA foundation evidence.
No new Lean declaration, axiom audit or CI acceptance is asserted for this class.
The project goal remains Fefferman D.

## The initial-data class

Fix viscosity $\nu>0$ and let

$$
\mathcal D_A=\mathcal S_\sigma(\mathbb R^3;\mathbb R^3)
$$

be the real divergence-free Schwartz data for the unforced Navier–Stokes
equations. No mean-zero condition is imposed. For $a\in\mathcal D_A$, let
$U^{a,\nu}$ be the canonical maximal $H^1$ strong/mild solution, with lifespan
$T_{\max}(a,\nu)\in(0,\infty]$. Define

$$
\tau_A(a,\nu)=\frac{8\|a\|_2^4}{27\pi^4\nu^5},
\qquad
b_A(a,\nu)=\min\{T_{\max}(a,\nu),\tau_A(a,\nu)\}.
$$

For $a\ne0$, the budget and its normalized gauge are

$$
J_A(a,\nu)=
\lim_{r\uparrow b_A(a,\nu)}
\int_0^r\|\nabla U^{a,\nu}(t)\|_2^4\,dt
\in[0,\infty],
\qquad
L_A(a,\nu)=(4\nu J_A(a,\nu))^{1/4}.
$$

For $a=0$, set $J_A=L_A=0$. The registered class is

$$
\boxed{\mathfrak C_\nu^A
=\{a\in\mathcal D_A:L_A(a,\nu)<\infty\}.}
$$

The full improper endpoint is essential. If $T_{\max}\le\tau_A$, the budget
includes possible divergence as $t\uparrow T_{\max}$. Finiteness on every
shorter compact interval does not establish membership.

## Six fixed whole-space charges

Order the three pairs $(-|\xi_j|,j)$ lexicographically, for $j=1,2,3$.
The six possible coordinate orderings partition frequency space into six
measurable sectors $C_1,\ldots,C_6$. Thus absolute coordinates are sorted in
decreasing order, with a smaller coordinate index first in a tie. Enumerate
the permutations as $123,132,213,231,312,321$.

Define the vector Fourier projections by

$$
\widehat{Q_\alpha f}(\xi)
=\mathbf1_{C_\alpha}(\xi)\widehat f(\xi),
\qquad \alpha=1,\ldots,6.
$$

These fixed projections are mutually orthogonal, resolve the identity and
commute with spatial derivatives. Every sector is invariant under
$\xi\mapsto-\xi$, so the projections preserve real fields. Their scalar
multipliers also preserve divergence-freeness. They are whole-space
projections; the periodic coordinate-average channels are a separate construction.

For the same canonical trajectory, put

$$
q_{\alpha,A}(t)=\|\nabla Q_\alpha U^{a,\nu}(t)\|_2^2,
\qquad
J_{6,A}(a,\nu)=
\lim_{r\uparrow b_A(a,\nu)}
\int_0^r\sum_{\alpha=1}^6q_{\alpha,A}(t)^2\,dt,
$$

with $J_{6,A}(0,\nu)=0$. Writing $Y(t)=\|\nabla U(t)\|_2^2$, orthogonality gives

$$
\sum_{\alpha=1}^6q_{\alpha,A}(t)=Y(t),
\qquad
\sum_{\alpha=1}^6q_{\alpha,A}(t)^2
\le Y(t)^2
\le6\sum_{\alpha=1}^6q_{\alpha,A}(t)^2.
$$

Integration over the full endpoint therefore yields

$$
J_{6,A}\le J_A\le6J_{6,A},
\qquad
4\nu J_{6,A}\le L_A^4\le24\nu J_{6,A}.
$$

In particular,

$$
\boxed{
a\in\mathfrak C_\nu^A
\iff
\int_0^{b_A(a,\nu)}
\sum_{\alpha=1}^6q_{\alpha,A}(t)^2\,dt<\infty.
}
$$

Here and below the terminal integral has the full improper meaning above.
Each charge is already a squared gradient norm. Each $q_{\alpha,A}(t)^2$ is
the fourth power of the gradient $L^2$ norm. The six projected fields are
components of the same solution, not independently evolving NSE solutions.

## Equivalence with global regularity

The recorded finite-window continuation argument gives

$$
\boxed{
a\in\mathfrak C_\nu^A
\iff J_{6,A}(a,\nu)<\infty
\iff T_{\max}(a,\nu)=\infty.
}
$$

Finite $J_A$ bounds the enstrophy by Gronwall and excludes
$T_{\max}\le\tau_A$, including equality. A small-product restart strictly
before $\tau_A$ then extends the same canonical trajectory globally.
Conversely, a global strong solution is continuous into $H^1$ on the compact
interval $[0,\tau_A]$, so its budget is finite.

For Schwartz data, the resulting velocity and normalized pressure are smooth
on every finite closed time slab, including the initial time, and
$\sup_{t\ge0}\|U(t)\|_2^2\le\|a\|_2^2$. Pressure is determined up to a smooth
function of time. Identification with the literal smooth finite-energy
Fefferman-A class uses the established closed-slab solution-class bridge
recorded as input A4 in the
[finite-window specification](../../Temp-folder/specification/FEFFERMAN_A_ELEMENTWISE_FINITE_WINDOW_B_TIER_v0_1.txt).

## Fourier normalization and sublevels

With $\widehat U(\xi)=\int e^{-2\pi i x\cdot\xi}U(x)\,dx$, interpreted by
$L^2$ extension, the full Fourier charge is

$$
Q_A[U](t)=\int_{\mathbb R^3}|\xi|^2|\widehat U(t,\xi)|^2\,d\xi
=\frac{Y(t)}{4\pi^2}.
$$

Consequently the WFA Fourier budget satisfies

$$
B_A(a,\nu)=\int_0^{b_A}Q_A[U](t)^2\,dt
=\frac{J_A(a,\nu)}{16\pi^4},
\qquad
L_A(a,\nu)^4=64\pi^4\nu B_A(a,\nu).
$$

For a finite $R\ge0$, define

$$
\mathfrak C_{\nu,R}^A
=\{a\in\mathcal D_A:L_A(a,\nu)\le R\}.
$$

These classes increase with $R$ and exhaust $\mathfrak C_\nu^A$:

$$
\mathfrak C_\nu^A=\bigcup_{n=1}^{\infty}\mathfrak C_{\nu,n}^A.
$$

This is a set-theoretic exhaustion. Membership depends on the canonical
evolution; no initial-data-only test, norm, linear-space structure or
compactness of these sublevels is asserted.

## Registered statements and evidence boundary

| Register name | Exact scope |
|---|---|
| NSE_A_FINITE_CHARGE_CLASS | Definition of $\mathfrak C_\nu^A$, the complete endpoint budget and its sublevels |
| NSE_A_SIX_CHARGE_CHARACTERIZATION | Six fixed real-preserving projections, charge additivity, factor-six comparison and the same finiteness class |
| NSE_A_FINITE_CHARGE_IFF_GLOBAL | Datumwise equivalence with global canonical strong regularity; the literal Fefferman interpretation retains A4 |

These are B-tier register names, not newly compiled Lean theorem names.
The analytic chain is based on E08–E10, Sections 13.2–13.6 and the soundness
addendum of the existing finite-window specification.

The [accepted QFA foundations](../QFA/README.md),
[name register](../QFA/QFA_FOUNDATIONS_A_TIER.txt) and
[external receipt](../../audits/material-afd67db4-qfa-accepted/summary.json)
retain their exact scopes at commit afd67db4, run 44788963412. Those results
do not formally establish this new six-projector construction, the complete
WFA continuation theorem, or the class equivalence above.

The remaining universal assertion is

$$
\boxed{\text{For every }\nu>0,\quad
\mathfrak C_\nu^A=\mathcal D_A.}
$$

It is equivalent to universal global regularity in the recorded solution
category and remains open. The class characterization does not prove that
every admissible datum belongs to the class.

## B-tier step list toward A-tier

The [twenty-endpoint plan](A_TIER_STEPLIST.md) gives the bottom-up route from
physical H1/Fourier adapters to the canonical class theorem and the literal
Fefferman-A identification. It separates the first pathwise spectral milestone
from the substantive NSE local theory and continuation proofs.
The [complete step-list derivation](NSE_A_A_TIER_STEPLIST_B_TIER.txt) records
source anchors and completion criteria; [A_TIER_PLAN.json](A_TIER_PLAN.json)
records dependencies and current status. The authorized plan has now reached
full P01–P07/G05 acceptance; P08 and the later PDE/class endpoints retain their
exact native obligations.

## Collected Lean sources for the missing proofs

The [Lean cutout collection](LEAN_CUTOUTS/README.md) supplies 51 exact reference
blocks and 60 full pinned source snapshots. Its [gap assessment](LEAN_CUTOUTS/GAPS.md)
identifies the largest missing native statements and the improved integral
Gronwall route. The cumulative step-list TXT links every cutout, retaining
all hypotheses and the separation between source availability and acceptance.


## Six closure targets and native construction

[Six target register](SIX_GAP_A_TIER_TARGETS.txt) · [Current implementation](SIX_GAP_IMPLEMENTATION_STATUS.json) · [Package assessment](SIX_GAP_PACKAGE_ASSESSMENT.txt).

G05 and the original P01–P07 scopes are complete. The three NSE-A batches
contain 16 accepted packages and289 names. P08's complete stopped-window,
improper-limit, Fourier normalization and gauge/sublevel interface is the
next native endpoint. G01,G02,G03,G04,G06 remain open.

## Construction and derivation record

The implementation register preserves every failed source/audit attempt,
its original evidence and its statement-preserving repair. The first nine
packages reached acceptance at3dec32be/run44810272232; the current seven-package
layer is accepted at the exact source and run displayed above.

Reviewed mathematical chains include [local/maximal H1](DERIVATIONS/H1_LOCAL_FIXED_POINT_CHAIN.txt),
[sharp spatial admission](DERIVATIONS/SHARP_SPATIAL_ADMISSION_CHAIN.txt),
[physical energy/enstrophy](DERIVATIONS/PHYSICAL_ENERGY_ENSTROPHY_CHAIN.txt),
[actual H2 graph reconstruction](DERIVATIONS/PHYSICAL_H2_GRAPH_CHAIN.txt),
[full stopped-window/gauge](DERIVATIONS/FULL_STOPPED_WINDOW_GAUGE_CHAIN.txt), and
[the literal closed-slab bridge](DERIVATIONS/FEFFERMAN_A_CLOSED_SLAB_CHAIN.txt).
Their native boundaries remain explicit. The real-H1 sector chain has reached
the accepted original G05 scope; the remaining analytical chains retain
B-tier status pending their own native construction and external evidence.
