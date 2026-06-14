---
name: i-orca-compile
description: Compile an i-orca proof (.i.orca.md) to a backend — Isar (primary, checkable .thy), TeX (always emits), or Lean 4 (best-effort skeleton). Holes lower to sorry. Use to produce the artifact a prover or human reads.
argument-hint: [file] [--target isar|tex|lean4]
allowed-tools: Read, Bash, mcp__i_orca__compile_proof
---

Compile an i-orca proof to a backend.

Run `i-orca compile <file> --target <isar|tex|lean4>` (or call `compile_proof`).
Default target is `isar`. For all theorems in one artifact, add `--document`
(`isar` → a single combined `.thy`; `tex` → one LaTeX document).

The three backends are asymmetric by design (SPEC §6):

- **isar** — PRIMARY and checkable. Lowers to a real `.thy`; `## context` rows
  become named assumptions so the theory is self-contained; holes → `sorry`.
  This is the artifact `i-orca check` / Isabelle kernel-checks.
- **tex** — secondary, *always emits* even for an incomplete proof; holes are
  annotated (e.g. `[hammer]`), never silently dropped.
- **lean4** — secondary, **structure only**. Carries the DAG and propositions as
  comments inside a compiling shell; methods do not transfer. Never present it
  as a Lean proof.

Show the output. If the user wants it on disk, pass `--out <dir-or-file>`.
