# Identities for the shortest Ehrenfest route

These are existing source declarations, in the order needed by the proposed nine-module scalar proof. Follow each ID for its exact declaration/proof cutout, import, hypotheses and complete pinned source context. The mathematical root and stopped witness remain unimplemented/unproved respectively.

| Order | Cutout | Use in the proposed proof | Required bridge |
|---|---|---|---|
| 1 | [MLB12 — `SingularClosure.canonicalGalerkinSolution`](cards/MLB12.md) | Canonical family at n+1 | Preserve the same datum, viscosity and smoothness proof. |
| 2 | [MLB08 — `SingularClosure.GalerkinSolution.coefficientEnstrophy_identity`](cards/MLB08.md) | D prime=-2 nu Z-2 P; e=D/2 | Transfer normalization; do not apply to forced error w. |
| 3 | [AUX02 — `HasDerivWithinAt.inv`](cards/AUX02.md) | Reciprocal derivative within Ici 0 | Prove 1+e/eStar is nonzero. |
| 4 | [ML06 — `HasDerivAt.inv`](cards/ML06.md) | Ordinary reciprocal derivative | Use only after passing to interior times if needed. |
| 5 | [ML05 — `HasFDerivAt.comp_hasDerivAt`](cards/ML05.md) | Chain rule for an explicit trajectory | Supply the actual canonical derivative. |
| 6 | [AUX04 — `HasDerivWithinAt.mono`](cards/AUX04.md) | Restrict derivative to Icc 0 T | Prove Icc 0 T is contained in Ici 0. |
| 7 | [AUX05 — `HasDerivWithinAt.hasDerivAt`](cards/AUX05.md) | Interior ordinary derivative | Use the interval-neighborhood fact; not at its endpoints. |
| 8 | [AUX06 — `HasDerivWithinAt.continuousWithinAt`](cards/AUX06.md) | Endpoint within-continuity | Retain the one-sided domain. |
| 9 | [AUX07 — `HasDerivWithinAt.continuousOn`](cards/AUX07.md) | Continuity on the closed slab | Assemble actual derivatives at its points. |
| 10 | [ML21 — `exists_hasDerivAt_eq_slope`](cards/ML21.md) | Single-cutoff terminal comparison | First derive PreHit for all interior times from R_n>C. |
| 11 | [MLB15 — `MethbokeAddon.WeakFouriermanB.global_smooth_to_initial_front`](cards/MLB15.md) | Global smooth solution gives an actual front | Take S=T+1, not an open front terminating at T. |
| 12 | [FAST02 — `SingularClosure.FINITE_FOURIER_H2_L1_BOUND`](cards/FAST02.md) | Projected C1 bound from finite Fourier l1 | Apply componentwise and to derivative coefficients; bound by reference H3. |
| 13 | [FAST03 — `SingularClosure.torusSobolevMultiplierLinear_norm_le`](cards/FAST03.md) | H1 Fourier tail from reference H2 | Build the complement multiplier and verify its symbol inequality. |
| 14 | [FAST05 — `SingularClosure.torusSobolevLeray_norm_le`](cards/FAST05.md) | Contract Leray projection of residual | Identify the physical residual with the Fourier representation. |
| 15 | [FAST04 — `SingularClosure.coefficientEnergy_le_dissipation`](cards/FAST04.md) | Finite mean-zero Poincare bound | Supply Parseval and spectral reality for the error. |
| 16 | [AUX01 — `SingularClosure.finiteSobolev_H1_physical_norm_sq`](cards/AUX01.md) | Arbitrary-coefficient H1/physical identity | Applicable to finite error coefficients once spectral reality is proved. |
| 17 | [MLB09 — `SingularClosure.coefficientEnstrophyNonlinearPower_eq_physical`](cards/MLB09.md) | Physical/Fourier nonlinear enstrophy sign | Keep A=-Delta and native power P=-W. |
| 18 | [FAST01 — `MethbokeAddon.WeakFouriermanB.PHYSICAL_NONLINEAR_ABSORPTION`](cards/FAST01.md) | Absorb the signed self-error term | Arbitrary smooth periodic mean-zero w qualifies; prove its forced-error identity separately. |
| 19 | [ML03 — `le_gronwallBound_of_liminf_deriv_right_le`](cards/ML03.md) | Scalar Gronwall bootstrap | Convert the actual derivative inequality to the required right-slope form. |
| 20 | [AUX03 — `HasDerivWithinAt.norm_sq`](cards/AUX03.md) | Within-domain norm-square calculus | Use finite-dimensional coefficient calculus or supply the actual derivative. |
| 21 | [ML08 — `HasDerivAt.norm_sq`](cards/ML08.md) | Interior norm-square calculus | Not a replacement for deriving the forced-error equation. |

## Exact normalizations

```text
D = coefficientDissipation,  e = D/2,
Z = coefficientLaplacianSquare,
P = coefficientEnstrophyNonlinearPower = -W,
e' = -nu*Z-P,
V = (1+e/eStar)^(-1),
V' = (nu*Z+P)/(eStar*(1+e/eStar)^2).
```

The reciprocal identity, forced-error evolution and final root are new compositions of these sources; no corresponding new compiled theorem is included. Under the hypothetical smooth-front bound choose one cutoff with R_n>C. Only then does the stopped guard hold throughout the open comparison interval. The mean-value theorem gives V(T)<=V(0)-gamma*T, which contradicts positivity at T=1/gamma.

## Operator identities are a separate collection

The OP01–OP12 cards supply native partial-operator domains, adjoint/closure/core vocabulary and smooth-test-function density. ML10/ML12 supply product calculus, while the Jacobian and convolution cards support later transport constructions. These are not prerequisites of the nine-module scalar root. None supplies the complete new self-adjoint NSE transport realization by itself.
