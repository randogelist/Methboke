R3 EHRENFEST — NEXT LAYER, INACTIVE PREPARED SOURCE

STATUS: UNVERIFIED. These .lean.txt files are deliberately excluded from active
Material imports, registry entries, source counts and the 111-name acceptance
scope. Reading or preparing them supplies no compiler or kernel evidence.

Intended constructed identity:
  partial_j (R_n u)(x) = R_n (D_{n,j} u)(x).
The proposed proof differentiates the actual inverse Fourier integral, uses
the positive inverse multiplier 2*pi*i*inner(xi,e_j), and identifies the
result with the native cutoff derivative. Ordered derivative words then give
  norm(partial_a(R_n u)(x)) <= bernsteinConstant(n)
    * (2*pi*(n+1))^length(a) * norm(u).
All constants are for a fixed cutoff. The candidate does not construct
nonlinear evolution, establish uniform comparison, admit the literal
NSE-A solution to physical Sobolev spaces, or prove the obstruction root.

The source, Endpoint and Audit are retained exactly as independently
statically reviewed. External compilation and all eight named type/axiom
audits remain mandatory before promotion.

PUBLIC DECLARATIONS
  MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fourierInv_integral_fderiv_apply
  MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_coordinate
  MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.fderiv_sharpCutoffRepresentative_physicalH2Gradient
  MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.cutoffWordCLM
  MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.norm_cutoffWordCLM_apply_le
  MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate
  MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative
  MethbokeAddon.R3Ehrenfest.DerivativeRepresentative.coordinateIterate_sharpCutoffRepresentative_bound
