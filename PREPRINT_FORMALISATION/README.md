# Preprint statement anchors

| Anchor | Statement | Present evidence |
|---|---|---|
| QFB-ROOT | Literal original eventual-tail contract | Inherited external Lean evidence; see index I01 |
| ANALYTIC-CYLINDER | Compact-cylinder bounds and strong initial trace | Complete B-tier derivation, section 3; actual compact Serrin and initial-trace proof sources prepared, external root recheck pending |
| FINITE-CAP | `D_Q(nu) subset R_nu` | Complete B-tier derivation, section 4; literal two-sided analytic data-class Lean root prepared, matching external acceptance pending |
| GERM-REDUCTION | `FB_nu iff (D_germ(nu) subset D_Q(nu))` | B-tier under recorded foundation interfaces; section 5 |
| BELTRAMI | Arbitrary-amplitude finite Fourier Beltrami admission | Explicit B-tier solution; section 7 and index I02 |
| WEAK-FOURIERMAN-B | Full finite squared Fourier budget implies global smooth continuation of the same trajectory | [B-tier v0.4.0](../Weak_Fourierman_B_B_TIER.txt); [candidate sources and workflow plan](WeakFouriermanB/README.md); Lean pending |
| UNIVERSAL-ADMISSION | `D_germ(nu) subset D_Q(nu)` | Open |

The [cumulative derivation](../CLAY_ADMISSION_CANDIDATE_01_B_TIER.txt) is the
mathematical source. [GPT.txt](../GPT.txt) identifies the dependency layers for
formalization. The exact candidate declaration is
`MethbokeAddon.WeakFouriermanB.D_Q_subset_R_nu` in
[R0DataAdmission.lean](../Material/MethbokeAddon/WeakFouriermanB/R0DataAdmission.lean).
Its admitted class contains zero and nonzero smooth data with an actual
two-sided analytic NSE cap at `2*tau_Q`; the equation uses the ordinary time
derivative throughout that cap. The general cap theorem also preserves both
the supplied forward velocity and normalized pressure. Initial trace, compact
Serrin integrability, finite-window comparison and smooth gluing have proof
sources; the universal existence of the required cap remains R1, which is open.

[External recheck 44545010863](https://github.com/randogelist/Methboke/actions/runs/44545010863)
at `c6e039da53283442393ecff1c6e125c880bdba7d` is pending. Earlier run
`44543421609` at `0ddd2d67` failed; two proof-syntax rewrites were corrected for
the recheck. These anchors record completed source preparation, without
asserting new A-tier acceptance, full Weak_Fourierman_B closure or a completed
preprint. No local Lean or tests were run. A later PDF belongs in
[PAPER_PREPRINT_PDF](../PAPER_PREPRINT_PDF/).

