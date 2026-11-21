# Whole-space full Leray–Hopf restart

**A-tier accepted at `ffbab0f5` / [run 44847013775](https://github.com/randogelist/Methboke/actions/runs/44847013775)** for the exact scoped declarations.
[Matching evidence](../../audits/material-ffbab0f5-qfa-accepted/independent-review.json). The general QFA root remains open.

The exact package source, independent expected types and named standard-only
axiom audits passed in the matching external run above.

The new source files preserve the original concrete contracts and prior
energy/selection sources. They construct the missing weak-PDE translation and
full class membership for a supplied path:

```text
LerayHopf nu a u G
+ 0 <= s
+ EnergyStart nu u G s
  => LerayHopf nu (u s) (fun t => u (t+s)) (fun t => G (t+s)).
```

The membership theorem requires no sign assumption on viscosity. Nonnegative
viscosity is needed by the retained strong-trace results, and positive viscosity
is retained by the safe-window result.

## Construction

1. Translate every actual smooth compact positive-time solenoidal momentum test
   by the backward clock t-s. Compact support and positivity are proved using
   the explicit affine homeomorphism and the source test's support.
2. Prove the time-derivative chain rule and exact spatial derivative identity.
3. Transport all three physical spatial contractions. Each original time
   integrability field is restricted to (s,infinity) and pulled back by the
   measure-preserving clock.
4. Prove that the translated test derivatives vanish on t<=s. Only then remove
   the discarded initial segment from the original weak momentum equation.
5. Transport the original a.e. spatial weak-gradient and all-upper-endpoint
   energy-start fields. The accepted energy-profile and weak-continuity helpers
   supply the other fields of the unchanged LerayHopf structure.
6. Intersect the a.e. restart fields and upgrade the original strict safe-window
   and half-window measure conclusions to include full shifted PDE membership.

The package contains 18 public declarations: one test constructor and 17
theorems. Independent audit consumers retain the actual affine clock, the
original concrete PDE predicates, the three literal contractions and the
squared L2 energy formula. Each declaration has a named type and axiom sentinel.

## Scope

The theorem assumes one original Leray–Hopf path and restarts that same path.
It does not establish global weak nonemptiness, local H1 existence, weak–strong
comparison, a Sobolev constant, small-product continuation or a smooth tail.
The complete physical QFA theorem remains a separate target.

No local Lean, Lake or kernel audit was executed. The unchanged compiler,
dependency lock, cache policy and allowed axiom list remain authoritative.
