# Actual H2 heat trajectory and time measurability

Status: A-tier accepted at `000c1bd9`, [external run 44851575278](https://github.com/randogelist/Methboke/actions/runs/44851575278).
Exact scope: 15 named declarations (14 theorems, 1 definitions).
[Matching independent review](../../audits/material-000c1bd9-qfa-heat-time-accepted/independent-review.json); the complete run
passed 526 modules, 105 fresh package audits and 1,402 unique named reports,
plus fresh QFB, complete publication and final acceptance.

The actual positive-time H1-to-H2 map is assembled into a real-time physical H2
trajectory. At nonpositive times it is extended by zero only to obtain a total
measurable map; an arbitrary H1 input is not claimed to have an H2 initial value.
At every positive time the velocity and H1 inclusion are the exact accepted
heat semigroup. A fixed positive smoothing step and H1 strong continuity prove
H2 continuity locally. Continuity away from time zero proves strong
measurability without a supplied regularity witness.

The physical H2 norm decomposes exactly into the heat H1 norm and actual
Laplacian norm. H1 contraction bounds the first term, leaving the true
Laplacian time-energy estimate for the next package. This scope alone does
not assert time-integrability or nonlinear NSE existence.

No local Lean, Lake or kernel audit is executed. General QFA remains open.
