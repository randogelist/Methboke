# Repository instructions

Read [GPT.txt](GPT.txt), [README.md](README.md) and
[INDEX-WORTHY.txt](INDEX-WORTHY.txt) before continuing work. `GPT.txt` is the
single project context document; amend it constructively with relevant source,
proof and evidence changes.

- Work from `main`. Preserve the fixed goal unless the user explicitly changes it.
- Follow the user's current BASE_LOOP. Discussion creates no artifacts; parser
  collection defers execution until the relevant compilation command.
- Never run Lean or Lake locally. Use authorized cached external CI or external
  native Windows replay. Preserve the pinned toolchain and dependency lock.
- Restore compatible objects, rebuild affected own modules, and freshly audit
  every required endpoint/type/axiom on each new verification run.
- Never rebuild Mathlib from source merely because its official object cache
  is unavailable. Report that obstruction. Do not delete compatible caches.
- Publish passed caches/containers only after the required build and fresh audit
  succeed. Keep inherited evidence separate from new matching verification.
- Preserve theorem statements, explicit premises and scope. Prepared files,
  cache hits or CI status alone do not prove the analytic continuation root.
- Synchronize GPT, README, relevant indices and status metadata before commits.
