# Weak_Fourierman_B

Repository workstream on `main`; preparation stage, 2026-11-19.

The target is the conditional implication from the full finite squared Fourier
budget up to `min(Tmax,Tf)` to global smoothness of the same trajectory, with
`Tf = ||a||_2^4/(8*pi^2*nu^5)`. Methboke's fixed analytic-admission goal is preserved.
Universal budget finiteness and universal analytic-germ extension remain open.

| Item | State |
|---|---|
| [Cumulative B-tier derivation](../../Weak_Fourierman_B_B_TIER.txt) | Version0.4.0; complete composition using indexed QFB and cited classical local theory |
| [Workflow plan](WORKFLOW_PLAN.md) | Staged migration preserving compatible baseline objects |
| [Ten contextual obligations](obligations.json) | All pending matching repository A-tier evidence |
| [Four source modules and audit requirements](candidate-sources.json) | Exact bytes staged; 1,255 lines, 57 declaration pairs |
| [Source map](SOURCE_MAP_v0_1.md) | Historical indexed lookup; mathematical gaps superseded by B-tier v0.4.0, Lean gaps remain |
| Active Material registration | Not changed; candidate sources are outside its discovery root |
| External WFB repository verification | Not run |

Candidate sources are under `candidate/src/MethbokeAddon/WeakFouriermanB/`.
Keep their namespaces/imports and do not substitute the old failed FourierBudget
from the original v0.1 payload. Neither embedded audit commands nor prepared
proof bodies are external verification.

The next implementation is the cache/failure-routing gate in the workflow plan,
then active module/audit registration and one external cached verification.
No local Lean execution is allowed. On external runner start, finish the turn;
`go on` resumes result inspection. There is no scheduled monitoring. Emit `<->`
in chat only for an exact contextual obligation or root after accepting all
matching external compiler/type/axiom evidence.
