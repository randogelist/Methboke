# QFASmallProductCoefficient

Prepared pointwise scalar helper for the strict small-product part of NSE-A G03.
Matching cached external compilation and independent named type/axiom evidence are
still required. No local Lean, Lake, kernel audit or runner was executed.

## Exact scope

From positive S and viscosity ν, a nonnegative supplied coefficient q, and

- q^4 ≤ S^6 W;
- W < ν^4 / S^6;

the package proves q < ν. A supplied balance d + 2νZ ≤ 2qZ then gives

- 0 < ν - q;
- d + 2(ν - q)Z ≤ 0;
- d ≤ 0 when Z ≥ 0, and d < 0 when Z > 0.

The zero-product endpoint derives q = 0 directly from the fourth-power premise
and W = 0. No division by W, q or Z is used.

## Six named endpoints

- `smallProduct_coefficient_lt_viscosity`
- `smallProduct_coefficient_eq_zero_of_product_zero`
- `smallProduct_retained_dissipation`
- `smallProduct_positive_gap_and_dissipation`
- `smallProduct_derivative_nonpos`
- `smallProduct_derivative_neg`

## Derivation and physical boundary

The B-tier chain was written first in
R3_NSE/A-Regularity-class/DERIVATIONS/PHYSICAL_ENERGY_ENSTROPHY_CHAIN.txt,
especially sections 6 and 9. The mathematical physical application takes
W = E Y and q = S6^(3/2)(E Y)^(1/4), after proving the actual spatial estimate.

This source does not prove that coefficient bound for a physical velocity,
construct a strong NSE solution, identify d with an actual derivative, establish
time absolute continuity, prove the invariant first-crossing argument, or prove
global continuation. It does not admit a sharp Sobolev constant. These remain
separate parent obligations; a successful audit of this package does not close G03.

## Independent external audit

Audit.lean repeats all six complete consumer types independently and expands the
threshold as ν^4 / S^6. Every endpoint has one exact TYPE_BEGIN/TYPE_END pair and
one AXIOMS_BEGIN/AXIOMS_END pair. Allowed axioms are propext, Classical.choice and
Quot.sound. The external source revision and actual verification result must be
recorded before changing the package's pending status.
