# Accepted FDSN_R3 evidence from main

This folder retains externally verified **main-branch** evidence in the
AC-Integration evidence archive. The tested proof source belongs to `main`;
this retention does not merge or import FDSNR3 proof modules into AC-Integration.

## Exact provenance

- Tested main source: `572fd9ee69a6b641f435cbfb2ef74e034809c583`.
- Git tree: `d5b0e6baa53c68c2d4c97e4f2f0843b76047eb07`.
- Matching external run: [44848985720](https://github.com/randogelist/Methboke/actions/runs/44848985720).
- Complete evidence artifact: `14684049987`, 400,034 bytes,
  SHA256 `320d05ae62963c329de38c4c570abef1a5e947e98dfe32ad2e3be43e78f76243`.
- Original routing artifact: `14685365223`,
  SHA256 `6924d19607101c695e71de3b37cf99595f10ee69c29fe24554a8c8c5f15dd99b`.
- Independent review JSON SHA256:
  `303c2723f806178aad27ad22e206b799707199fe3af851451cab3119c78d1097`.
- Compiler: Lean 4.33.0 on external x86_64 Linux.
- Mathlib: `db584cd6d46c92f209a44c0f1c829460d327499d`.

All **548 modules passed** (46 fresh, 502 reused), with **137 fresh package
audits and 1,320 unique named literal type/axiom reports**. The original QFB
cutout, required publication and final acceptance gate all passed. The
independent text/JSON/hash review passed 11,541 checks, including reconstruction
of all 548 module source/import identities and all 137 audit source identities.
Only `propext`, `Classical.choice` and `Quot.sound` occur in named axiom reports.

## Accepted mathematical scope

All **R3-01 through R3-16** are accepted for the original conditional whole-space
construction. The exact root is

```lean
MethbokeAddon.FDSNR3.FDSN_R3 :
  ∀ {ν T : ℝ} {u F : SingularClosure.Velocity} {p : SingularClosure.Pressure},
    MethbokeAddon.FDSNR3.Seed ν T u p F →
      MethbokeAddon.FDSNR3.Family ν T u p F
```

The FDSNR3 scope contains 26 packages and 493 named declarations: 391 theorems
and 102 definitions, abbreviations or structures. All 497 independent literal
consumers passed, including the fully expanded Family consumer. Beyond the
previously accepted 72-name foundation, this accepts 23 packages with 421 names
(354 theorems and 67 definitions, abbreviations or structures). The original
Seed/Family contracts and verification policy are byte-preserved from the
accepted `4d00e260e82368b9d9abbec7e14ce32844f8f7dc` foundation.

The root assumes the explicit local-Schwartz compact-local-blowup Seed; **native
seed existence remains open**. It constructs one physical family with all the
original clauses, preserving the same initial velocity, pressure and terminal
tail. Forces vary with the family parameter. Rapid spatial decay is included;
compact spatial force support is not asserted. The separate stronger
prescribed-site same-force family, **general QFA and general WFA remain open**.

## Retained evidence and reproduction

`evidence.zip` contains the complete original compiler/type/axiom logs and
receipts. `routing-evidence.zip` contains the original publication routing.
Authenticated artifact/run/job metadata and the final gate log are retained
unchanged. The complete FDSNR3 declaration evidence is compressed in
`fdsn-declaration-evidence.json.gz`; its name/type-hash index and the compressed
root audit are retained separately. All eleven evidence/reviewer files are
byte-identical to the independent review originals.

Run the reviewer against a repository containing the exact tested main Git
objects and the accepted foundation objects:

```sh
python3 /path/to/this/folder/review_evidence.py /path/to/Methboke /path/to/this/folder
```

The reviewer reads immutable Git objects and ZIP/JSON/text evidence, hashes
bytes and writes derived review files. It does not execute Lean, Lake, a local
kernel audit, or any repository compiler script. It may regenerate compressed
package logs from the unchanged original archive. Local Lean executions: **0**.
