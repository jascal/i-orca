---
name: i-orca-prove
description: Drive the i-orca autonomous loop on a proof (.i.orca.md) — verify → compile Isar → check against a warm Isabelle session → hammer open obligations — climbing formal_fraction toward 1.0. Degrades gracefully when Isabelle is absent.
argument-hint: [file]
allowed-tools: Read, Bash, mcp__i_orca__verify_proof, mcp__i_orca__check_proof, mcp__i_orca__hammer_step
---

Drive the i-orca prove loop (SPEC §7) toward a kernel-checked proof.

The loop:

1. `verify_proof` (cheap, no Isabelle) → refine until structurally valid.
2. `compile_proof isar` → the `.thy`.
3. `check_proof` (warm Isabelle session) → per-step real status + open
   obligations as structured prompt fragments.
4. For each open obligation: `hammer_step(step_id)` → on success, splice the
   reconstructed `by (metis …)`; on failure, refine that step and retry.
5. Repeat until `formal_fraction_real → 1.0`.

CLI shortcut: `i-orca prove <file> --out <dir>` runs steps 1–3 and writes the
`.thy` artifacts.

**Graceful degradation:** if no Isabelle distribution is found, `check`/`hammer`
return `available: False` with the static fallback — steps 1–2 still run, so CI
and the fast refine loop never break. Set `ISABELLE` / `ISABELLE_HOME` (or put
`isabelle` on `PATH`) to enable the kernel path.

**Honesty:** report `formal_fraction_static` (estimate) and, when available,
`formal_fraction_real` (kernel truth) separately. Their gap is the metric
(SPEC §8). Only steps with status `checked` are actually proved.
