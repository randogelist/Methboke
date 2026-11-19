# Preprint statement anchors

| Anchor | Statement | Present evidence |
|---|---|---|
| QFB-ROOT | Literal original eventual-tail contract | Inherited external Lean evidence; see index I01 |
| ANALYTIC-CYLINDER | Compact-cylinder bounds and strong initial trace | Actual compact Serrin integrability and initial trace accepted at `93ca8a5`; the separate numerical integral bounds in section 3 remain B-tier |
| FINITE-CAP | `D_Q(nu) subset R_nu` | Exact two-sided analytic data-class root accepted with matching external compiler, type and axiom evidence at `93ca8a5`; B-tier derivation in section 4 |
| GERM-REDUCTION | `FB_nu iff (D_germ(nu) subset D_Q(nu))` | B-tier under recorded foundation interfaces; section 5 |
| BELTRAMI | Arbitrary-amplitude finite Fourier Beltrami admission | Explicit B-tier solution; section 7 and index I02 |
| WEAK-FOURIERMAN-B | Full finite squared Fourier budget implies global smooth continuation of the same trajectory | [B-tier v0.4.0](../Weak_Fourierman_B_B_TIER.txt); [candidate sources and workflow plan](WeakFouriermanB/README.md); Lean pending |
| UNIVERSAL-ADMISSION | `D_germ(nu) subset D_Q(nu)` | Open |

The [cumulative derivation](../CLAY_ADMISSION_CANDIDATE_01_B_TIER.txt) is the
mathematical source. [GPT.txt](../GPT.txt) identifies the dependency layers for
formalization. The exact accepted declaration is
`MethbokeAddon.WeakFouriermanB.D_Q_subset_R_nu` in
[R0DataAdmission.lean](../Material/MethbokeAddon/WeakFouriermanB/R0DataAdmission.lean).
Its admitted class contains zero, handled by the explicit zero solution, and
nonzero smooth data with an actual two-sided analytic NSE cap at `2*tau_Q`.
That cap remains an explicit admission premise; its equation uses the ordinary time
derivative throughout that cap. The general cap theorem also preserves both
the supplied forward velocity and normalized pressure. Initial trace, compact
Serrin integrability, finite-window comparison and smooth gluing have matching
external verification. R1, extending every local analytic germ through the
required cap, remains open. The BAMBUS/Beltrami construction and universal
germ reduction remain B-tier, as do the separate numerical integral bounds.

[Accepted external run 44549257770](https://github.com/randogelist/Methboke/actions/runs/44549257770)
checked `93ca8a57536512556ec36717ee933ea52db283bf`. The
[retained evidence](../audits/material-93ca8a5/summary.json) records 321 modules,
303 objects reused, 18 additions built, 33 fresh endpoint-package audits,
161 declaration audits plus the QFB cutout, and 183 passed external controls.
The exact root uses only `propext`, `Classical.choice` and `Quot.sound`.
Historical runs `44543421609` at `0ddd2d67` and `44545010863` at `c6e039da`
failed before the accepted proof-syntax and inference corrections; neither
is acceptance evidence. This R0 acceptance does not assert full
Weak_Fourierman_B closure or a completed preprint. No local Lean or tests were
run. A later PDF belongs in
[PAPER_PREPRINT_PDF](../PAPER_PREPRINT_PDF/).

