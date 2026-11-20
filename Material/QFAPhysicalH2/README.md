# Actual physical H2 graph and exact norms

This package constructs the full-volume real H2 graph from the already
accepted compact-test weak derivative. Its ambient Hilbert space has exactly
thirteen vector-L2 entries: velocity, three first derivatives, and nine
ordered second derivatives. Closed continuous test-pairing kernels prove
completeness. The actual velocity determines the entire graph uniquely.

The construction includes continuous maps from H2 to physical H1 and from
each first derivative to physical H1, the closed native solenoidal
restriction, and admission of actual real Schwartz fields. The L2 Laplacian
is the diagonal sum of the Hessian. Its equality with the native tempered
distributional Laplacian is proved from the existing first-derivative
transport, so the old spectral interface is constructed from the graph.

Applying the accepted first-derivative Fourier theorem twice proves the
literal second-derivative symbol, mixed-derivative symmetry and the complete
nine-term norm density. Plancherel then gives

```
sum_j sum_k ||H_jk||_2^2 = ||L||_2^2
||u||_H2^2 = ||v||_2^2 + sum_j ||G_j||_2^2 + ||L||_2^2.
```

The full Fourier norm keeps the exact factors `4 * pi^2` and `(2 * pi)^4`.
Genuine weighted integrability is proved. No Fourier norm identity,
Hessian symmetry, compact-to-Schwartz adapter, or extra derivative witness
is assumed in a theorem about the constructed physical H2 graph.

## Evidence scope

The two owned modules expose 65 named declarations: 45 theorems and
20 definitions, abbreviations and instances. `Audit.lean` contains 78
independent consumers, literal full-volume carrier and compact-test
expansions, the explicit closed graph, native solenoidal predicate,
unchanged coordinate maps, actual distributional Laplacian, and all exact
Fourier formulas. Every name has ordered full-type and axiom sentinels.

The package is **prepared pending matching cached external verification**.
No local Lean, Lake, kernel or runner was executed. Accepted H1, sector,
Fourier and dependency source bytes are unchanged.

This is a spatial foundation for P09 and the H2 regularity carrier needed
by P10. It does not complete the sharp Sobolev estimate, construct an NSE
evolution, prove a finite temporal budget, or close the full finite-charge
equivalence. Reconstruction from H1 plus only an L2 distributional
Laplacian is a separate next module, not a premise hidden in this graph.

Derivation: `R3_NSE/A-Regularity-class/DERIVATIONS/PHYSICAL_H2_GRAPH_CHAIN.txt`.
