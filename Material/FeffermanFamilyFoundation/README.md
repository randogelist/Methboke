# Periodic Fefferman D family foundations

This is the first implementation layer toward `Fefferman_D`, using the
finite-site family route documented in
[T3_NSE/D-Family-Obstruction](../../T3_NSE/D-Family-Obstruction/README.md).
The implementation is prepared for matching external cached verification.
It does not yet construct a smooth-force singular seed or prove
`Fefferman_D_Family_obstruction`.

| Source | Implemented scope |
|---|---|
| `LocalBlowup.lean` | Quantitative local velocity blowup, compact growth-sequence localization, and obstruction to a continuous extension |
| `DisjointGerms.lean` | Finite supported sums locally equal one copy or zero, including spacetime germs and support-boundary points |
| `FamilyContracts.lean` | Actual native forced NSE, ordinary smoothness, periodic pressure and velocity, finite torus-site configurations, bounded preterminal energy, and scoped contract helpers |

The native files are in `Material/MethbokeAddon/FeffermanFamily/`. They contain
28 public helper theorems. This package independently checks their full consumer
signatures and expands 11 key definitions/structures literally. Each of these
39 names receives fresh exact-type and standard-axiom reports in `Audit.lean`.
The family existence statement is only a definition. Its projection theorem
retains that statement as an explicit premise; it does not supply a witness.
The zero-force exclusion helper verifies that the nonexistence contract rejects
the native zero solution as a counterexample.

`Endpoint.lean`, `endpoint.json` and `closure.json` register the package in the
existing Material runner. `owned-sources.json` hashes the three new sources.
`endpoints.json` preserves the preceding 71 packages and 448 declaration audits
and adds this package, giving 72 packages and 487 named audits, plus the existing
QFB cutout. The projected build count is 415 modules: the previous 411 plus
three sources and one endpoint wrapper. Audit modules are executed separately.
These counts describe the planned scope, not an observed compiler result.

Compiler and dependencies remain Lean `4.33.0` and Mathlib
`db584cd6d46c92f209a44c0f1c829460d327499d`. No Lake configuration, workflow,
vendor proof, previous audit entry or cache policy changes. The implementation
is rebased onto `c483fe0683e443b42c93c6bf00d37613567b0d03`; original development
context remains pinned to `aacfe7c4b0dc9f1642269823c174de74d7097fcb`.
An origin entry identifies that baseline context, not a claim that the new
proof bytes already existed in it.

`static-validation.json` records file, manifest, dependency-metadata and audit
coverage checks only. The complete retained repository is checked by the
existing external runner. No local Lean, Lake or kernel audit was executed.
Only matching external compiler, complete type/axiom and source evidence may
promote these helpers. The singular seed import, copy transformations, packing,
PDE gluing, energy, periodization and same-force uniqueness remain future layers.
