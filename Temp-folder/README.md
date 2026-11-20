# AC-Integration: staged endpoints

This folder contains the source and evidence inputs requested for the QFA/WFA
whole-space integration. The working branch is `AC-Integration`, created from
Methboke `66a529248d3198ed70dc5489d82868bc33a37796`. The retained project goal
is **Fefferman_D**; this branch's immediate task is source and evidence preparation.

## Start here

- [Ten-step QFA/QFB construction checklist](QFA_QFB_10_STEP_CHECKLIST.md): current proposed construction order, with QFB as the accepted periodic reference.
- [Endpoint dependency map](ENDPOINTS.md): concrete source locations and 15 proposed obligations.
- [Component manifest](MANIFEST.json): archive hashes, revisions and extraction provenance.
- [File inventory](FILE_INVENTORY.json): SHA-256 of every other file staged in this folder.
- [B-tier mathematical specification](specification/FEFFERMAN_A_ELEMENTWISE_FINITE_WINDOW_B_TIER_v0_1.txt).

## Original archives and unpacked contents

| Input | Original ZIP | Unpacked content |
|---|---|---|
| October core, 85 files | [MasterAC v0.11](archives/FEF_NSE_MASTERAC_TWO_LAYER_LEAN_v0_11_0.zip) | [Core and historical endpoints](unpacked/FEF_NSE_MASTERAC_TWO_LAYER_LEAN_v0_11_0/) |
| Concrete closure, 3 files | [ABCD closure v0.25](archives/FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0.zip) | [Concrete definitions and endpoint layer](unpacked/FEF_NSE_ABCD_A_TIER_UNIFIED_CLOSURE_LEAN_v0_25_0/) |
| Tested periodic source, 782 files | [Methboke fdb515d8 export](archives/METHBOKE_QFB_WFB_SOURCE_fdb515d8.zip) | [Complete pinned project source](unpacked/METHBOKE_QFB_WFB_SOURCE_fdb515d8/) |
| Accepted external evidence, 129 files | [Exact evidence ZIP](archives/material-evidence-fdb515d8bde35ec8021bbc26f360aca8dfa2855c-44566880192-1-fast.zip) | [Report, audit logs and receipts](evidence/material-fdb515d8/) |

The original ZIPs are preserved. October extraction removes one leading
archive directory. The Methboke export is pinned to
`fdb515d8bde35ec8021bbc26f360aca8dfa2855c`; all 782 unpacked files match its Git
blob identities. GitHub exported 15 `run.cmd` files with CRLF; their unpacked
copies were restored to the exact pinned Git bytes. The original export and
each transformation are recorded in [provenance](provenance/).

## Endpoint locations

The October concrete module imports `Fefferman.Analysis` and
`Fefferman.Statements` from v0.11. Version 0.25 includes the complete v0.24
closure source, so v0.24 is not duplicated here.

Within the pinned Methboke snapshot, start with:

- `Material/_vendor/QuasiFeffermanB/Endpoints/Root.lean` and `RootContract.lean`.
- `Material/MethbokeAddon/WeakFouriermanB/WeakFouriermanB.lean`.
- `Material/_vendor/SingularClosure/` for the physical analytic dependencies.
- The `Material/QFB*/` and `Material/WFB*/` endpoint packages and their audits.

The full snapshot retains the dependency context of these modules. Its old
AGENTS, goal documents and runner instructions are archival context; current
branch instructions and status are in the repository's root documents.

## Integration status

This folder is reference staging outside the active `Material` build. Source
copies and existing periodic audit results do not verify new QFA/WFA declarations.
The actual R3 solution theory, continuous Fourier identity, restart and
continuation instances remain explicit integration obligations. The universal
WFA budget remains open. The October global-regularity port is a target
interface whose analytic premise still needs proof.

No Lean, Lake, local kernel audit or included runner was executed. No new
external verification was dispatched. Existing active proof sources, compiler
pins, dependencies and workflows remain as inherited from the branch base.

The optional compiled cache is catalogued in [EXTERNAL_CACHE.json](EXTERNAL_CACHE.json).
It remains an external Linux-CI artifact; it is not needed to inspect these
sources, and it is not a native Windows cache.
