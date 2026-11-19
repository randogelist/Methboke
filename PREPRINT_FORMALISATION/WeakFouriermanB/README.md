# Weak_Fourierman_B

Repository workstream on `main`; active registration awaiting external verification, 2026-11-19.

The target is the conditional implication from the full finite squared Fourier
budget up to `min(Tmax,Tf)` to global smoothness of the same trajectory, with
`Tf = ||a||_2^4/(8*pi^2*nu^5)`. Methboke's fixed analytic-admission goal is preserved.
Universal budget finiteness and universal analytic-germ extension remain open.

| Item | State |
|---|---|
| [Cumulative B-tier derivation](../../Weak_Fourierman_B_B_TIER.txt) | Version0.4.0; complete composition using indexed QFB and cited classical local theory |
| [Workflow plan](WORKFLOW_PLAN.md) | Owned-source activation and explicit receipt/failure policy |
| [Ten contextual obligations](obligations.json) | WFB-01/WFB-02 accepted at0402aa37; eight and root remain open |
| [Four source modules and audit requirements](candidate-sources.json) | Exact bytes active; 1,255 lines, 57 declaration pairs |
| [Source map](SOURCE_MAP_v0_1.md) | Historical indexed lookup; mathematical gaps superseded by B-tier v0.4.0, Lean gaps remain |
| Active Material registration | Four owned modules and four packages; 18 total packages / 98 audits |
| External WFB repository verification | First layer PASS: [44537934256](https://github.com/randogelist/Methboke/actions/runs/44537934256); SmoothDatum pending |

Candidate sources are under `candidate/src/MethbokeAddon/WeakFouriermanB/`.
Keep their namespaces/imports and do not substitute the old failed FourierBudget
from the original v0.1 payload. Neither embedded audit commands nor prepared
proof bodies are external verification.

The next step is external cached verification with all required audits.
Physical local H1 existence remains the first missing substantive formal edge;
see [the exact source review and independent datum helper](next/REVIEW.md).
No local Lean execution is allowed. The user authorizes continued independent
implementation while external CI runs and active inspection when results arrive. There is no scheduled monitoring. Emit `<->`
in chat only for an exact contextual obligation or root after accepting all
matching external compiler/type/axiom evidence.
