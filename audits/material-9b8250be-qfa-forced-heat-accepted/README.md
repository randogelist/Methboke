# Accepted actual L2 Duhamel response, forcing operator and spatial energy

**!=! A_TIER_MATCHING_EXTERNAL_ACCEPTED_EXACT_SCOPES**

Tested source `9b8250be2f13048e3e21cd94c8ba1939d919bf64`, tree
`5e8f0db8caa9063d149922ad571fea7d594a735d`,
[external run 44857358591](https://github.com/randogelist/Methboke/actions/runs/44857358591).

The cached external verification passed **534 modules, 109 fresh package audits,
and 1435 unique named type/axiom reports**. Complete publication, standalone
QFB and the final acceptance gate passed. Only `propext`, `Classical.choice`
and `Quot.sound` occur in the named transitive audits. The independent
nonexecuting source/import/closure/hash/raw-report review passed 10872 checks.

## Exact new scope

| Package | New declarations | Literal consumers | Accepted scope |
|---|---:|---:|---|
| QFAHeatDuhamel | 15: 14 theorems, 1 definition | 17 | Actual retarded SpatialL2 integral for finite-window MemLp2 forcing; integrand measurability/integrability, zero trace, AE invariance, linearity, exact square-root time/forcing-norm bounds and continuous response on the closed window. |
| QFAHeatDuhamelOperator | 5: 4 theorems, 1 definition | 7 | Actual bounded linear map from the time-L2 forcing quotient to continuous SpatialL2 paths, literal integral, norm at most sqrt(T), zero trace and compatibility with every admissible representative. |
| QFAHeatSpatialEnergy | 4 theorems | 5 | Actual physical H1 integration by parts, H1-H2 Green pairing, H2 bilinear Laplacian symmetry and exact negative-enstrophy self-pairing. |

Total: **24 new declarations = 22 theorems + 2 definitions; 29 consumers**.
The source assumptions are the actual physical carriers and genuine forcing
MemLp2; no supplied solution, derivative, integrability or continuity witness
is introduced. Bilinear symmetry is not an unbounded self-adjoint-domain claim.

## Retained authenticated evidence

Original complete artifact 14688452213: 2193723 bytes, SHA256
`8a484eff336ac8151405b7034ae4b88b787efa7f8f03dc2cd19a42d1ebc0c60f`.
Original routing artifact 14688083841: 577 bytes, SHA256
`dd08d0a291ddfec5576b68f0cffcb5cc2b253caf4f25a84513aa6c07b21358d7`.
Independent review SHA256
`15b45ede95d03bfe45e415f4df70775003de20218d8597c0cfa80c01ac56e332`.

The original ZIPs, authenticated artifact metadata, matching completed run/jobs,
final-gate log, independent reviewer, all 24 new named type/axiom records and
three package logs are retained. Prior failed runs 44855166853, 44856232687 and
44856945923 remain recorded with their exact minimal elaboration repairs.

## Boundaries

This batch does not prove the inhomogeneous velocity derivative equation,
forced H1/H2 maximal regularity, nonlinear H1 local existence, sharp S6
admission, general LH nonemptiness or physical weak--strong comparison.
Only whole checklist steps 1 and 7 remain complete. General QFA, WFA, the
open G-parent targets and the separate D-family goal are unchanged.

Accepted generator, heat-time and conditional main FDSN_R3 receipts are
preserved. All previously accepted proof/audit/closure and verification-policy
bytes are unchanged. No local Lean, Lake, kernel audit or dependency rebuild
was performed.
