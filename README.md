# Clay-Admission-Candidate-01

`MODE = B_TIER_DERIVATION` · `NO_LOCAL_LEAN` · `NEW_ROOT_A_TIER = NOT_ESTABLISHED`

## Exact scope

Unforced incompressible Navier–Stokes on the unit three-torus; viscosity `nu > 0`; smooth, divergence-free, mean-zero initial data.

`D_germ(nu)` consists of initial data admitting an actual jointly space-time analytic NSE germ through time zero. `D_Q(nu)` consists of data admitting such an analytic solution on `(-epsilon, 2*tau_Q)`, with the zero datum included separately, where

```text
tau_Q(a,nu) = ||a||_2^4 / (8*pi^2*nu^5).
```

## B-tier conclusions

| Statement | Status |
|---|---|
| Finite analytic cylinder implies finite Serrin norm and strong initial trace | `!=B_TIER`; explicit compactness estimate |
| `D_Q(nu) subset R_nu` | `!=B_TIER`; actual QFB tail plus finite weak–strong comparison and overlap patching |
| Finite Fourier Beltrami data belong to `D_Q(nu)` | `!=B_TIER`; explicit arbitrary-amplitude solution |
| `D_germ(nu) subset D_Q(nu)` | Unresolved universal continuation obligation |
| Universal germ-to-cap admission is equivalent to periodic Fefferman B under the stated local/analytic/QFB interfaces | `!=B_TIER`; exact reduction |
| New-root compiler pass / theorem-level axiom audit | None |

## Deliverables

- [Material](Material/README.md): 14 exact endpoint folders, complete vendored local source closures, standalone cutout export, cached external compilation and passed-container registry.
- [Material CI](.github/workflows/material.yml): push-triggered compilation, type/axiom audits, incremental container reuse and immutable GHCR endpoint tags.
- [CLAY_ADMISSION_CANDIDATE_01_B_TIER.txt](CLAY_ADMISSION_CANDIDATE_01_B_TIER.txt): definitions, complete mathematical derivations, explicit admitted family, and remaining root.
- [Mathlib reuse audit](audits/MATHLIB_REUSE_AUDIT.txt): exact declarations, source pins, signatures and scope limits.
- [Methlib QFB reuse audit](audits/METHLIB_QFB_REUSE_AUDIT.txt): actual physical endpoints and matching archived compiler evidence.
- [Methlib analytic reuse audit](audits/METHLIB_ANALYTIC_REUSE_AUDIT.txt): finite-window adapters and named unresolved premises.
- [QFB dependency audit](audits/METHLIB_QFB_DEPENDENCY_AUDIT.json): 256-module source/blob comparison.
- [Source and status manifest](SOURCE_STATUS.json).

## Material rebuild contract

`push -> last compatible PASS image -> changed modules + dependents -> exact axiom audit -> immutable registry tags`.

The branch cache pointer advances only when `previousPASS <= candidate <= HEAD` in commit ancestry. A newer queued commit can therefore reuse the just-completed predecessor. A documentation-only amendment has no Lean source changes; its CI run must preserve matching compiled objects and audit evidence while still executing Lake validation and the measured no-op rerun. Runtime and cache-reuse claims require the resulting external evidence; preparation alone remains `A_TIER_CANDIDATE`.

## Dependency constraints

Methlib's inspected lock: Lean `4.33.0`, mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`.

The archived QFB external run identifies Linux Lean `4.33.0`, 71 verified object-cache hits, and root axioms `[propext, Classical.choice, Quot.sound]`. The 256 audited local source modules match the compiled QFB/foundation snapshots. This is inherited evidence for QFB; it is not native Windows evidence or evidence for the new root.

Future native Windows formalization must retain a compatible compiler, manifest and cache, and produce exact new-root compiler and axiom-audit evidence. No local Lean command was executed.

## Excluded closure shortcut

```text
QFBAdmissions.OneRestartOverlapAxiom
  axiom QFB_ONE_RESTART_OVERLAP : QFBOneRestartOverlapStatement
```

`OneRestartOverlapCertificate.local_overlap_closes` must be constructed from actual local solutions and overlap identification. Its existence is not implied by interval arithmetic or by naming the certificate.

`UNCONDITIONAL_CLOSURE = NOT_ESTABLISHED`.
