# WFBSmoothDatum

`STATUS = PENDING_EXTERNAL_CI` · `NO_LOCAL_LEAN`

Smooth periodic solenoidal mean-zero physical datum embeds into the original QFB EnergySigmaZero class, with actual representative equality, literal cutoff identity, and original Leray-Hopf existence. This is only the WFB-08 input adapter.

The owned source matches the current candidate in
`PREPRINT_FORMALISATION/WeakFouriermanB/next/SmoothDatum.lean`. It derives from
the staged source at `0402aa37ea09f90a216e63e5fe67c3f58bb2b844`, with one
proof-only equality-transitivity repair recorded in `../owned-sources.json`.
The theorem signatures and premises are unchanged.
Its complete import closure has 182 source modules, including the one owned module.

`Audit.lean` freshly checks all seven declarations with complete type and
axiom records. It independently states the principal existence and cutoff
signatures. External source/compiler/dependency/audit evidence is required
before acceptance; only standard axioms are allowed.

Even a successful audit completes only the smooth-datum input bridge.
WFB-08 additionally needs identification of the same weak and strong path on
finite intervals. Local strong existence, maximality, continuation and the
Weak_Fourierman_B root remain separate obligations.
