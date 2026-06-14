---
name: i-orca-verify
description: Structurally verify an i-orca proof (.i.orca.md) — DAG, scope, discharge, cases/induction, naming — with zero Isabelle. Use before compiling to Isar or firing the prover. A green result means well-formed, NOT proved.
argument-hint: [file]
allowed-tools: Read, Bash, mcp__i_orca__verify_proof
---

Structurally verify an i-orca proof document.

If $ARGUMENTS is a file path, run `i-orca verify <file>` (or read it and call
`verify_proof` with the contents). If it is raw `.i.orca.md` source, pass it
directly.

After verification:

- **If valid:** confirm, then report `formal_fraction_static` and the list of
  *frontier holes* (steps marked `hammer`/`sketched`). Make clear these are the
  formalization frontier, not errors.
- **If invalid:** list every error with its stable code, message, and
  suggestion, grouped by severity (error / warning / advisory). Offer to refine.

**Load-bearing honesty (SPEC §2, §11.5):** a green verify means the proof
*skeleton* is well-formed — a decidable, strictly-weaker property. It does **not**
mean the proof is true. Never present `verify` output as a proof. The kernel
verdict comes only from `i-orca check` against a real Isabelle session.
