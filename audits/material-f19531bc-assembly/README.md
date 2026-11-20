# Native periodic-family assembly acceptance

[External run 44663707207](https://github.com/randogelist/Methboke/actions/runs/44663707207)
tested `f19531bca6816cea31c687629b9ab73ee6868169` and passed the final Material gate.
The [summary](summary.json) and [independent review](independent-review.json)
record the exact source, compiler, type, axiom and publication evidence.

Accepted scope: **22 helper theorems and one speed-predicate definition**.
They establish explicit growth-sequence selection, compact localization,
geometric blowup transport, native differential-operator locality, and exact
finite disjoint forced-NSE assembly. This evidence does not establish a
singular seed, family existence or the literal Fefferman-D root. The separate
direct-D workflow is outside this record.

| Observed item | Result |
|---|---|
| Compiled modules | 420: 415 reused, 5 fresh |
| Fresh package audits | 73; none reused |
| Named type/axiom reports | 510, plus fresh QFB |
| New scoped declarations | 22 helper theorems + one definition |
| Axiom policy | Only `propext`, `Classical.choice`, `Quot.sound` |
| External control tests | 183 passed |
| Independent evidence checks | 4,995 passed |
| Core verification | 156.035 seconds |
| Worker job wall time | 296 seconds |
| Cache classes | Dependencies EXACT; project PREFIX |

The preceding 415 module receipts and 487 named type/axiom maps are preserved.
The four repaired source files retain their intended mathematical signatures;
compiler evidence applies to the repaired tested revision only. No local Lean,
Lake or kernel audit was executed.

The original [evidence archive](evidence.zip) preserves all 108 artifact members,
including the complete report, module receipts, plans and fresh audit logs.
The focused [assembly audit](FeffermanFamilyAssembly.log),
[losslessly compressed worker log](fast-job.log.gz), and
[final acceptance log](acceptance-job.log) are also retained. File digests and
the uncompressed worker-log digest are recorded in the summary.

These are observed results for this run, not a performance guarantee or an
exact-cache benchmark. A later evidence-only commit is not a new compiler run.
