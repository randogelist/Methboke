# Fourth QFA integration attempt: proofs pass, registration rejected

At commit 76376e08, external run 44787324841 compiled all 463 modules and
freshly audited all 77 packages, covering 698 named declaration reports plus
the standalone QFB cutout. All six new native modules and their independent
type consumers passed.

The final evidence/publication gate correctly rejected the checked-in
endpoint index: it retained 73 entries and omitted the four new QFA packages.
No passed cache was published and no new A-tier acceptance is recorded.
The next revision adds the four registrations without changing any proof,
audit source, compiler, dependency or verification policy, then obtains a
matching complete external run. Full raw evidence and fast-job log are retained.
