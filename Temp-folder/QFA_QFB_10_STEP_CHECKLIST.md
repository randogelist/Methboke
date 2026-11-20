# QFA/QFB: ten-step construction checklist

Date: 2026-11-20. Branch: **AC-Integration**.

**Purpose:** construct the whole-space QFA theorem alongside the accepted
periodic QFB theorem, with the same four-part structure: weak existence,
eventual smoothness, tail energy equality, and uniqueness from each tail trace.

This is the requested construction plan. The source collection is complete.
The ten boxes below concern the new construction and remain open; preparing
this plan does not begin formalization or supply new A-tier evidence.
The retained repository project goal is Fefferman_D.

## Fixed sources and exact scope

The QFB reference is **QuasiFeffermanB.QUASI_FEFFERMAN_B_COMPOSED** at
Methboke commit **fdb515d8bde35ec8021bbc26f360aca8dfa2855c**, with matching
external run **44566880192** and artifact **14553501775**.
Its [root contract](unpacked/METHBOKE_QFB_WFB_SOURCE_fdb515d8/Material/_vendor/QuasiFeffermanB/RootContract.lean),
[root proof](unpacked/METHBOKE_QFB_WFB_SOURCE_fdb515d8/Material/_vendor/QuasiFeffermanB/Endpoints/Root.lean),
and [external report](evidence/material-fdb515d8/current.json) are staged here.

The QFA mathematical target is Section 13.1 (E12) of the
[cumulative B-tier specification](specification/FEFFERMAN_A_ELEMENTWISE_FINITE_WINDOW_B_TIER_v0_1.txt).
All constants and analytic inputs below refer to that specification.

| Feature | QFA construction target | Frozen QFB reference |
|---|---|---|
| Domain and data | $L^2_\sigma(\mathbb R^3)$, with no periodic mean-zero condition | Physical $L^2_{\sigma,0}(\mathbb T^3)$, represented on the unit cube |
| Cutoff | $\tau_A=\frac{8}{27\pi^4}\frac{\|a\|_2^4}{\nu^5}$ | $\tau_B=\frac{\|a\|_2^4}{8\pi^2\nu^5}$ |
| Shared main clause | Every specified LH path; every $\delta>\tau_A$ | Every specified LH velocity/weak-gradient pair; every $\delta>\tau_B$ |
| Closed cutoff detail | The B-tier argument also supports $\delta=\tau_A$, including zero data | The frozen root separately supplies smoothness at safeCutoff $=2\tau_B$; its main energy/uniqueness clause remains strict |
| Future uniqueness | From the exact trace of the selected path | From the exact trace of the selected path |

Smoothness means existence of a classical representative agreeing spatially
almost everywhere at every tail time. It does not impose smoothness on every
arbitrary representative of an $L^2$ class.
The shared structure is not an equivalence between the A and B domains.

Write $E=\|u\|_2^2$, $Y=\|\nabla u\|_2^2$,
$Z=\|\Delta u\|_2^2$, and $E_0=\|a\|_2^2$.
All whole-space integrals use Lebesgue measure on $\mathbb R^3$.

## The ten construction steps

- [ ] **1. Fix the concrete QFA contract against the accepted QFB contract.**

  Define the actual whole-space datum, velocity, weak-gradient, distributional
  NSE, pressure and Leray–Hopf predicates. State the four-part QFA conclusion
  for every $\nu>0$, every $a\in L^2_\sigma(\mathbb R^3)$, every specified
  LH path and every $\delta>\tau_A(a,\nu)$. Record the additional closed
  safe-cutoff conclusion separately.

  **Complete when:** the exact types retain all quantifiers and physical
  equations, use the correct representatives, and impose no periodic
  mean-zero or spectral-gap condition on whole-space data. The contract
  defines the target without assuming its analytic conclusions.
  **Map:** O01. **QFB reference:** Semantics and RootContract.

- [ ] **2. Establish the whole-space spatial estimates and constants.**

  Supply Sobolev, interpolation, the vector/tensor norm extension, and
  $\|D^2u\|_2=\|\Delta u\|_2$. Prove admissibility of $S_6$ in
  $\|f\|_6\le S_6\|\nabla f\|_2$, with the numerical specialization
  $S_6^6=16/(27\pi^4)$ used by the target cutoff.

  **Complete when:** these are proved estimates for the actual whole-space
  spaces. A calculation on an extremal alone does not prove admissibility.
  The scalar argument may first use an arbitrary proved admissible $S_6$;
  the advertised numerical cutoff remains pending until its stated
  specialization is justified. **Map:** O02. **Character:** substantial
  whole-space analysis.

- [ ] **3. Construct local $H^1$ strong solutions and prove continuation.**

  Prove actual local existence, uniqueness, maximal lifetime, continuity in
  $H^1$, sufficient $L^2_tH^2_x$ control, bounded-$H^1$ continuation,
  positive-time smoothing and normalized-pressure recovery. The initial
  datum at this stage is an $H^1_\sigma$ restart trace.

  **Complete when:** local existence and continuation are proved for the
  physical NSE, with a usable maximality/extension theorem. A record carrying
  these conclusions as unproved premises does not complete this step.
  Schwartz regularity of the original QFA datum is not required.
  **Map:** relevant part of O04. **Character:** substantial whole-space
  solution theory.

- [ ] **4. Construct global Leray–Hopf solutions and admissible restart traces.**

  For every $L^2_\sigma$ datum, establish global LH nonemptiness, weak
  $L^2$ continuity, strong initial attainment, the energy inequality from
  zero and almost every starting time, and a full-measure set of solenoidal
  $H^1$ restart traces with right strong $L^2$ continuity.

  **Complete when:** shifting a specified solution from an admissible time
  yields the required LH solution from that exact trace. Energy control only
  from time zero is insufficient for this restart conclusion.
  **Map:** O05. **QFB references:** Q01_LERAY_HOPF_EXISTENCE,
  lh_strong_right_trace_of_energy_start, LH_RESTART_FROM_ENERGY_START,
  and LH_RESTART_AE_Ioo.

- [ ] **5. Prove weak–strong uniqueness from the same restart trace.**

  Compare the classes from steps 3 and 4 on every finite common interval.
  Show that a specified LH path agrees with the strong continuation from
  its exact restart datum.

  **Complete when:** equality holds in the chosen $L^2$ representatives at
  every relevant time, including the initial trace, rather than only at
  almost every time. The theorem must apply to the concrete whole-space
  solution classes without an unproved comparison hypothesis.
  **Map:** O06. **QFB reference:** the comparison and identification used by
  TAIL_REFERENCE_FROM_EXACT_ADMISSION.

- [ ] **6. Prove global strong continuation from a small energy–enstrophy product.**

  Derive the actual strong energy and enstrophy balances. Establish the
  nonlinear bound
  $$
  \left|\int_{\mathbb R^3}(u\cdot\nabla)u\cdot\Delta u\right|
    \le S_6^{3/2}(EY)^{1/4}Z.
  $$
  Prove that $E(s)Y(s)<\theta(\nu):=\nu^4/S_6^6$ gives a global strong
  continuation from $u(s)$.

  **Complete when:** the strict inequality supplies the fixed positive
  margin $\nu-S_6^{3/2}[E(s)Y(s)]^{1/4}$, the bootstrap keeps $E$ and
  $Y$ nonincreasing, and step 3 excludes a finite terminal time.
  **Map:** O07 and O09. **Character:** actual PDE balances followed by a
  reusable scalar bootstrap.

- [ ] **7. Prove the weighted-energy integral bound.**

  From the LH energy inequality, derive for every finite $T\ge0$
  $$
    \int_0^T E(t)Y(t)\,dt\le \frac{E_0^2}{4\nu}.
  $$
  Use the absolutely continuous majorant
  $A(t)=E_0-2\nu\int_0^tY(r)\,dr$, with $0\le E\le A$ almost everywhere.

  **Complete when:** the proof obtains
  $\int_0^T AY=(E_0^2-A(T)^2)/(4\nu)$ with all integrability and
  representative conditions discharged. It does not differentiate the
  possibly nonsmooth weak-solution energy $E$.
  **Map:** O10. **Character:** reusable scalar and measure-theoretic analysis.

- [ ] **8. Select a good restart strictly before the explicit cutoff.**

  Set
  $$
    \tau_A=\frac{S_6^6E_0^2}{2\nu^5}
          =\frac{8}{27\pi^4}\frac{\|a\|_2^4}{\nu^5}.
  $$
  For nonzero data, prove
  $$
    \left|\{t\in(0,\tau_A):E(t)Y(t)<\theta\}\right|\ge\tau_A/2>0.
  $$
  Intersect this set with the full-measure admissible-restart set from step 4.

  **Complete when:** an actual $s\in(0,\tau_A)$ has all trace, energy,
  solenoidality and $H^1$ properties needed in steps 5 and 6.
  Treat $a=0$ separately: $\tau_A=0$, and energy forces the zero path.
  **Map:** O11. **QFB references:** GoodTime and LHRestart; their periodic
  admission constants are not the whole-space constants.

- [ ] **9. Construct the closed smooth tail and prove tail energy equality.**

  Restart globally at the selected $s$, identify that continuation with
  the specified LH solution, and produce smooth velocity and normalized
  pressure representatives on $\mathbb R^3\times[\tau_A,\infty)$.
  For every finite $t\ge\delta\ge\tau_A$, prove
  $$
    E(t)+2\nu\int_\delta^tY(r)\,dr=E(\delta).
  $$

  **Complete when:** the safe cutoff is included because $s<\tau_A$;
  the zero branch is also covered. Identify weak and smooth gradients
  almost everywhere in time when transferring energy. Do not require
  correctness of an arbitrarily chosen weak-gradient value at the single
  time $\delta$.
  **Map:** tail part of O12. **QFB references:** TailRegularity and TailEnergy.

- [ ] **10. Prove unique future from every tail trace and assemble QFA alongside QFB.**

  For each specified LH path and $\delta\ge\tau_A$, prove that the shifted
  original path belongs to $\mathrm{LH}_\nu(u(\delta))$, and
  $$
    w\in\mathrm{LH}_\nu(u(\delta))
    \quad\Longrightarrow\quad
    w(r)=u(\delta+r)\quad\text{in }L^2,\ \forall r\ge0.
  $$
  Assemble LH nonemptiness, smooth tail, energy equality and future
  uniqueness into the whole-space QFA endpoint. Expose its strict-tail
  presentation alongside the unchanged accepted QFB endpoint.

  **Complete when:** every constituent is discharged by the preceding
  results, the translated path is included as a member of the future class,
  and the exact root types preserve domain and cutoff conventions.
  Uniqueness is from each path's own trace; it does not identify the tail
  traces of distinct original weak solutions.
  **Map:** remaining part of O12 and root assembly.
  **QFB references:** LH_RESTART_OF_TAIL_ENERGY,
  LH_UNIQUE_FUTURE_OF_SMOOTH_FLOW, TailChain and Endpoints/Root.

## Dependency order and A-tier completion rule

Steps 2–5 establish the spatial and solution-theoretic foundation.
Step 6 uses steps 2–3. Step 7 uses step 4. Step 8 uses steps 2, 4 and 7.
Step 9 combines steps 3, 5, 6 and 8. Step 10 adds tail restart and a new
weak–strong comparison from each tail trace.

The heaviest unresolved work is the actual whole-space analytic instance:
Sobolev estimates, strong and weak existence, admissible restarts and
weak–strong comparison. Periodic proofs provide precise construction
patterns and some reusable scalar lemmas; they do not discharge these
whole-space instances by renaming.

For each new formal endpoint, retain the exact source revision and use
authorized cached external CI or external native Windows. Completion
requires matching compilation, fully elaborated theorem types, theorem-level
axiom reports, and inspection of the discharged analytic instances.
An axiom report alone does not expose an unproved result carried as a
theorem parameter or record field. Preserve the existing Lean 4.33.0 and
Mathlib db584cd6d46c92f209a44c0f1c829460d327499d identities.

Local Lean, Lake invoking Lean, local kernel audits and archived runners
remain prohibited. No new verification run is part of this planning update.
Implementation follows the user's endpoint-assent workflow.

## Separate follow-on work

The [broader fifteen-obligation map](ENDPOINTS.md) is retained.
The continuous Fourier charge (O03), explicit initial-window certificate
(O08), full-budget cutoff crossing (O13), WFA (O14), and literal global
Fefferman-A bridge (O15) are subsequent tasks. They are not prerequisites
for the QFA tail theorem. Universal WFA-budget finiteness remains open.

The October concrete closure port remains an interface. This checklist
does not fill its globalZeroForce field or assert global smoothness from
time zero for arbitrary whole-space data.
