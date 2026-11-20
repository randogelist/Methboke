# QFA: accepted whole-space foundation integration

**Status: A-tier accepted for the exact foundation scopes below.**
The complete physical QFA and WFA theorems remain open.

Tested commit: `afd67db40e71bd1412c82247a78598288deb611e` on `AC-Integration`.
Matching [external run 44788963412](https://github.com/randogelist/Methboke/actions/runs/44788963412) passed compilation, fresh
signature/type/axiom audits, exact publication checks and final acceptance.
The [receipt](../../audits/material-afd67db4-qfa-accepted/summary.json),
[independent review](../../audits/material-afd67db4-qfa-accepted/independent-review.json) and
[complete new declaration evidence](../../audits/material-afd67db4-qfa-accepted/new-declaration-evidence.json)
fix the accepted source and statement scope. The project goal remains Fefferman D.

## Accepted native layers

| Layer | Source | Scope |
|---|---|---|
| Physical contracts | `Material/MethbokeAddon/QuasiFeffermanA/Contracts.lean` | Actual full-volume L2, compact-test weak derivatives, solenoidal momentum tests and standard LH fields; no existence or regularity conclusion is inserted |
| Energy and traces | `Energy.lean` | Weighted product budget, strong initial/right traces, energy restart data and zero-datum velocity rigidity for supplied paths |
| Scalar cutoff | `Cutoff.lean` | Positive scalar threshold, exact half-budget identity, good-time selection and half-measure bound |
| Physical energy-class selection | `Integration.lean` | A genuine solenoidal weak-gradient energy trace strictly before the scalar cutoff; full shifted weak-PDE membership remains separate |
| Fourier multipliers | `FourierMultipliers.lean` | Five owned derivative-witness proofs; the exact original failed upstream port is retained inactive |
| Spectral realization | `Spectral.lean` | Derivative witnesses imply Fourier norm identities and the native spectral endpoint, without assumed norm identities or spectral realization |

The native package has **35 accepted public helper theorems and 19 checked
contracts/definitions**. The four new packages supply 188 named reports:
108 recovered QFA declarations, 14 representation declarations, 12 historical
conditional-root declarations, and 54 native declarations. All 698 names across
77 packages were freshly audited; all 463 required modules passed, with 420
prior modules reused and 43 compiled. There are 58 independent new consumers
(55 native and three historical-root consumers). Only the standard axioms
`propext`, `Classical.choice` and `Quot.sound` occur. No local Lean was executed.

## Exact finite-window result

For a supplied `LerayHopf nu a u G` path, put

$$E(t)=\|u(t)\|_2^2,\qquad Y(t)=\sum_{j=1}^3\|G_j(t)\|_2^2,\qquad M=\|a\|_2.$$

For every finite $R>0$, the product is integrable and

$$\int_0^R E(t)Y(t)\,dt\le\frac{M^4}{4\nu}.$$

For arbitrary $S>0$ and $\nu>0$, define

$$\theta=\frac{\nu^4}{S^6},\qquad
\tau=\frac{S^6M^4}{2\nu^5}.$$

Then $M^4/(4\nu)=\theta\tau/2$. If $a\ne0$, at least half the window
consists of genuine energy/weak-gradient good traces with $E(s)Y(s)<\theta$.
In particular there is $0<s<\tau$ with solenoidality, all three weak-gradient
witnesses, the energy inequality from $s$ to every later endpoint, translated
energy/trace data and strong right convergence to $u(s)$.

This is a pathwise selection theorem. It assumes a supplied LH path and does
not construct one. Its energy inequalities are standard defining LH assumptions,
not conclusions derived from the weak momentum equation alone. `GoodRestart`
does not assert the translated weak momentum equation or full shifted LH membership.

The explicit premise $S^6=16/(27\pi^4)$ gives the algebraic rewrite
$\tau=8M^4/(27\pi^4\nu^5)$. Admissibility of this Sobolev constant and the
physical continuation threshold remain unproved here. For zero datum the cutoff
is zero and every supplied LH velocity vanishes at every nonnegative time;
the rigidity theorem does not construct a zero solution or pressure.

## Spectral scope

The spectral inputs are L2 fields with first-derivative and L2 Laplacian
identities against Schwartz test functions. The velocity itself need not be
Schwartz. The proofs derive the almost-everywhere Fourier multipliers, both norm
densities, weighted integrability and Plancherel energy identities, thereby
inhabiting `WholeSpaceSpectralEndpoint`.

Native LH traces supply first weak derivatives almost everywhere; the current
bridge does not manufacture an L2 Laplacian for every such trace. Physical H1/H2
adapters and the remaining spatial estimates are separate obligations.

## Ten-step construction status

| Step | Accepted scope | Remaining construction |
|---|---|---|
| 1. Concrete contract | Full-volume L2, solenoidality, compact-test weak gradients, projected weak momentum and LH energy-class interface | Pressure formulation and the complete current physical root contract |
| 2. Spatial analysis | Fourier multipliers and the spectral endpoint from first-derivative and L2 Laplacian distribution witnesses | Physical H1/H2 bridges, Hessian identity, Sobolev/interpolation admissibility and the stated sharp constant |
| 3. Local H1 theory | No new whole-space constructor accepted | Existence, uniqueness, smoothing and continuation |
| 4. LH solutions and restarts | Strong initial/right traces and translated energy/trace data for supplied LH paths | Global nonemptiness and full shifted-LH membership |
| 5. Weak-strong uniqueness | Recovered abstract comparison statements retain their premises | Actual R3 relative-energy inequality and comparison |
| 6. Small-product continuation | Scalar threshold arithmetic | Physical evolution estimates, invariant bootstrap and global continuation |
| 7. Weighted budget | Product integrability and one-quarter weighted bound for every finite positive horizon of a supplied LH path | The zero-length interval is not separately packaged; global LH existence belongs to step 4 |
| 8. Finite-window selection | Half-window measure, strict interior good trace, strong right trace and zero-datum rigidity | Admissible physical threshold and full PDE restart |
| 9. Closed smooth tail | No new physical tail theorem accepted | Classical representative, pressure and tail energy equality |
| 10. Full QFA conclusion | Historical conditional root retained with its original assumptions and cutoff | Future uniqueness from each path's own trace and assembly of the current physical QFA root |


The historical corrected root retains class realization, comparison,
Agmon, reference-construction and smoothness inputs, and its old strict cutoff
$M^4/(16\pi^2\nu^5)$. The new spectral proof inhabits one input interface;
it does not discharge the others. Periodic QFB remains an accepted reference
with its original scope. This integration does not assert an A/B equivalence.

## Evidence and retained history

The exact 35 recovered vendor sources are retained with per-file provenance;
33 are active and the original failed multiplier source and barrel remain
inactive. All 495 previously tracked native Lean files and all existing
compiler/dependency/driver policies remain unchanged from the integration basis.

The four earlier attempts are retained under `audits/`: the first exposed
cutoff and upstream multiplier elaboration failures; the second exposed scalar
conversion failures; the third isolated private spectral algebra; the fourth
passed all proofs and audits but was rejected for missing package-index entries.
The accepted run includes the corrected index. No failed run was promoted.

See [QFA_FOUNDATIONS_A_TIER.txt](QFA_FOUNDATIONS_A_TIER.txt) for the complete
accepted native name register and [INTEGRATION_STATUS.json](INTEGRATION_STATUS.json)
for the machine-readable boundary. Evidence-only later commits do not replace
the tested revision or claim a new compiler run.
