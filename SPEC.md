# i-orca — Specification (design proposal)

> **Status:** design proposal, not yet implemented. Drafted 2026-06-04.
> This document captures the design so the ideas are not lost; nothing here is built.
> i-orca is a proposed new dialect of the [Orca](../orca-lang) language family.

i-orca is a **Markdown-table DSL for writing mathematical proofs at the register LLMs
naturally produce** — more structured and machine-readable than human prose, more informal
than Lean tactic mode — whose **canonical backend is Isabelle/Isar**, with **TeX** and
**Lean 4** as secondary exports.

---

## 1. The conceptual frame

```
i-orca : Isabelle  ::  n-orca : PyTorch  ::  orca-lang : XState
```

A Markdown-table spec layer over a powerful-but-verbose execution substrate, adding **cheap
static verification before you run the heavy backend**. The difference from n-orca: PyTorch
always "runs" once shapes check; Isabelle "running" means *proving*, which can fail at a
semantic level no static check reaches. That partiality is the whole `sorry`/`formal_fraction`
story below.

### Why Isar is the right primary backend

1. **The semantic gap nearly closes.** Isar's declarative register
   (`have NAME: "P" using FACTS by METHOD`, `obtain`, `moreover`/`ultimately`,
   `proof (cases …)`) *is* the structured-but-readable level LLM proofs live at. An i-orca
   proof row **is** an Isar `have`. i-orca → Isar is transliteration; i-orca → Lean was
   translation.
2. **Sledgehammer is the discharge engine.** Isabelle's Sledgehammer dispatches each subgoal
   to external ATPs (E, Vampire, CVC5, Z3) and reconstructs a checked `by (metis …)`/`by (smt …)`.
   It is the most mature "fill the gap automatically" tool in any prover — the back half that
   a proof-sketch DSL otherwise has to hand-wave.
3. **The primary backend checks itself.** Isabelle's kernel gives i-orca a real soundness
   anchor on its main path, not just a human referee (TeX) or a best-effort transpile (Lean).

---

## 2. Design thesis: structural linter, not proof checker

Orca's load-bearing move is *separate the part you can decide cheaply from the part you can't,
and verify the cheap part before spending effort on the expensive one.*

| Orca core | i-orca |
|-----------|--------|
| **Topology** — the FSM graph (decidable: reachability, determinism) | **Proof skeleton** — the dependency DAG of claims, case tree, induction structure, scoping (decidable: graph + scope checks) |
| **Computation** — arbitrary action functions (never verified) | **Step validity** — whether each inference is actually *true* (undecidable; delegated to Isabelle's kernel or a human) |

**The loud disclaimer:** i-orca is a *structural linter + scaffold compiler*, **not a proof
checker.** It verifies the proof skeleton's well-formedness — a strictly weaker, decidable
property — and delegates truth to the backend. A structurally-valid i-orca proof **can be
mathematically false**, and it looks authoritative. A green `verify` must never read as
"proved." i-orca raises the floor (catches the structural nonsense LLMs produce) without
ever claiming the ceiling (truth).

---

## 3. Formality register: incompleteness is first-class

A gap is a `sorry`, not a failure. The verifier distinguishes two things sharply:

- **Ill-formed** → true errors, block the Isar lowering: circular dependency, forward
  reference, hypothesis used out of its case/binder scope, iff proved one direction, a goal
  neither discharged nor explicitly `sorry`'d.
- **Incomplete** → first-class, gradeable, *never* an error: a step whose method is prose-only
  or explicitly a hole. This is the **formalization frontier**, reported as a number, not
  rejected.

This is what lets one artifact span the register: some rows are Isar-ready, some cite a lemma,
some are honest holes — and the verifier reports the *mix* instead of demanding the proof be
fully formal.

### Step status lifecycle

| Status | Meaning | In `formal_fraction`? |
|--------|---------|-----------------------|
| `sketched` | `Claim` + `By` prose only, no method | no (NL-only) |
| `hammer` | marked for Sledgehammer (a structured hole) | no (frontier) |
| `method` | explicit Isar method present, expected to check | counts toward static estimate |
| `checked` | Isabelle confirmed (populated by a backend run) | yes (real) |
| `failed` | method present but Isabelle rejected it | no — surfaced as a real error |

---

## 4. Grammar

A document declares one or more `# theorem Name` blocks; files end `.i.orca.md`. Sections are
`##` headings. Tables carry the structured skeleton; prose lives in `>` blockquotes and the
`By` column.

### Sections

- `## imports` — Isabelle theories to import (→ Isar `imports`). One column: `Theory`.
- `## context` — named ambient facts (declared lemmas/defs assumed available). Columns:
  `Name | Statement`. Doubles as the namespace for `UNKNOWN_LEMMA_REFERENCE` and as
  Sledgehammer relevance hints.
- `## goal` — the proposition to prove. One column: `Statement`.
- `## proof [(method)]` — the step DAG. Optional outer method on the heading
  (e.g. `## proof (rule ccontr)`, `## proof (induction n)`). Rows are steps.
- `## case <name>` / `## base` / `## step (ih: …)` — scoped sub-blocks for case splits and
  induction. Each opens its own scope (local `fix`/`assume`); the verifier tracks visibility.

### The proof-step row schema

```
| Id | Claim | By | Using | Method | Status |
```

- **Id** — step name; becomes the Isar fact name (`have Id: …`). Unique within scope.
- **Claim** — the proposition. **The single source of truth**: Isar `have` type, TeX
  statement, Lean `have` type all derive from it. Prose never overrides it.
- **By** — the intermediate-register informal justification (human reason / lemma name).
  *Not decoration:* it becomes the prompt context when Sledgehammer is fired at this step.
- **Using** — comma-separated step/fact ids this step depends on. **This column is the
  dependency DAG** the verifier checks, *and* it lowers to Isar `using`, which is
  Sledgehammer's relevance filter. One annotation, two consumers.
- **Method** — optional Isar proof method (`simp`, `auto`, `(metis …)`, `blast`,
  `sledgehammer`, `sorry`). Present + checks → in `formal_fraction`; `sledgehammer`/`sorry`
  → frontier hole.
- **Status** — lifecycle (§3); authored as intent, overwritten by backend runs.

### Worked example

```markdown
# theorem SqrtTwoIrrational
> √2 is irrational.

## imports
| Theory       |
|--------------|
| Complex_Main |

## context
| Name         | Statement              |
|--------------|------------------------|
| even_sq_even | even (n^2) ⟹ even n    |

## goal
| Statement           |
|---------------------|
| Irrational (sqrt 2) |

## proof (rule ccontr)
| Id | Claim                      | By                       | Using    | Method               | Status  |
|----|----------------------------|--------------------------|----------|----------------------|---------|
| s0 | sqrt 2 = p/q, coprime p q  | unfold rational, reduce  | —        | sledgehammer         | hammer  |
| s1 | 2 * q^2 = p^2              | clear denominators       | s0       | sledgehammer         | hammer  |
| s2 | even (p^2)                | from s1                  | s1       | simp                 | method  |
| s3 | even p                    | even_sq_even             | s2       | (metis even_sq_even) | method  |
| s4 | p = 2*k                   | def of even              | s3       | blast                | method  |
| s5 | even q                    | substitute, even_sq_even | s1,s4    | sledgehammer         | hammer  |
| s6 | 2 dvd gcd p q ⟹ False    | contradicts coprime      | s0,s3,s5 | simp                 | method  |
```

lowers mechanically to (illustrative — methods/holes shown, not a certified proof):

```isabelle
theory SqrtTwoIrrational
  imports Complex_Main
begin

theorem sqrt2_irrational: "Irrational (sqrt 2)"
proof (rule ccontr)
  assume "¬ Irrational (sqrt 2)"
  obtain p q :: int where s0: "q ≠ 0" "sqrt 2 = p/q" "coprime p q"  sorry   (* hammer *)
  have s1: "2 * q^2 = p^2"  using s0  sorry                                  (* hammer *)
  have s2: "even (p^2)"     using s1  by simp
  have s3: "even p"         using s2  by (metis even_sq_even)
  obtain k where s4: "p = 2*k"  using s3 by blast
  have s5: "even q"         using s1 s4 sorry                                (* hammer *)
  show False               using s0 s3 s5 by simp
qed
end
```

### Row → Isar lowering table

| i-orca | Isar |
|--------|------|
| `## proof` heading | `proof - … qed` (or the declared `(rule …)`/`(induction …)`) |
| step row `Id / Claim / Using / Method` | `have Id: "Claim" using Using by Method` |
| `Method = sledgehammer` or `sorry` | `sorry` (+ a TODO marker; the prove loop fills it) |
| existential `Claim` with named witness | `obtain <vars> where Id: "Claim" using … by …` |
| `## case c` / `## base` / `## step (ih: …)` | `proof (cases …)` / `case … / induction` blocks; `ih` is a scoped fact |
| final step targeting the goal | `show <goal> using … by …` |
| `## context` row | a referenced fact name (resolved against the session, not emitted) |

---

## 5. The static verifier

Decidable, runs with **zero Isabelle**, emits stable LLM-actionable codes.

| Class | Codes | Catches (real LLM failure modes) |
|-------|-------|----------------------------------|
| DAG | `CIRCULAR_DEPENDENCY`, `FORWARD_REFERENCE`, `ORPHAN_STEP` | the proof that assumes its conclusion; "by s7" where s7 is later |
| Discharge | `UNDISCHARGED_GOAL`, `IFF_ONE_DIRECTION`, `EXISTS_NO_WITNESS` | "we have shown X" never derived; → for an ↔; existential with no witness |
| Scope | `HYP_OUT_OF_SCOPE`, `VAR_UNBOUND` | reusing a case-local assumption globally; free var never `fix`'d |
| Cases/Induction | `NON_EXHAUSTIVE_CASES`, `INDUCTION_MISSING_BASE`, `INDUCTION_MISSING_STEP` | the case split that quietly drops a case |
| Naming | `UNKNOWN_LEMMA_REFERENCE` | citing a lemma not in `## context` and not resolvable |

**Decidable vs degrades-to-advisory.** `NON_EXHAUSTIVE_CASES` and the scope checks are
decidable only when the splitting principle / domain is *declared* (a cited disjunction or a
typed `cases`). Free-form "Case 1: rational, Case 2: irrational" can only be confirmed
exhaustive if the disjunction is named. Where it isn't, the check degrades to **advisory**
(parallel to n-orca symbolic dims being "opaque but consistent").

**Isabelle is the sound backstop; the static layer is a latency accelerator.** Isabelle's
`consider`/`cases`/`induction` already enforce exhaustiveness and scope at elaboration. So the
static verifier catches *nothing Isabelle can't* — its value is catching it **cheaply, in
stable codes, without spinning up Isabelle**, so the LLM refine loop is fast and CI is
Isabelle-free. This is a UX/latency win, not a new guarantee. (Stated honestly per §11.)

---

## 6. The three backends (asymmetric by design)

- **Isar — primary, checkable.** Lowers to a real `.thy`. Holes → `sorry`. Isabelle elaborates
  and kernel-checks; Sledgehammer discharges holes. This is "compile to a runnable artifact,"
  where runnable = provable.
- **TeX — secondary, always emits, two routes.** (a) i-orca renders LaTeX directly even for an
  *incomplete* proof (the early/human path); (b) once the `.thy` is valid, **Isabelle's own
  document preparation** typesets the *checked* proof. Prefer (b) once it exists — the
  human-readable artifact is then the machine-verified one.
- **Lean 4 — secondary, "further exploration."** Best-effort **skeleton** transfer: carries the
  DAG and the propositions, `sorry`s the methods (Isar `metis`/`smt` have no clean Lean analog;
  HOL vs Mathlib lemma names differ). Honest claim: cross-prover portability of the *structure*,
  never of the proof.

---

## 7. The MCP surface (the primary way an LLM touches i-orca)

MCP is not an add-on — it is the delivery mechanism. The product is `source: string` in →
structured JSON out, with stable codes designed as a **feedback channel for an agent loop**.
For i-orca it matters more than for any sibling because the backend is the slowest and most
stateful in the family, and the MCP server is what hides that.

### Tool surface

| Tool | Isabelle? | Latency | Returns |
|------|-----------|---------|---------|
| `parse_proof(source)` | no | ms | AST JSON: steps, DAG edges, scopes, goal |
| `verify_proof(source)` | no | ms | `{valid, errors[], frontier[], formal_fraction_static, dag}` |
| `compile_proof(source, target)` | no | ms | `isar`\|`tex`\|`lean4` source (holes → `sorry`) |
| `refine_proof(source, errors)` | LLM | s | structurally-fixed source |
| `check_proof(source)` | **yes (warm)** | s–min | per-step *real* status + open obligations |
| `hammer_step(source, step_id)` | **yes (warm)** | bounded s | `{success, method: "by (metis …)"}` for one hole |
| `--tools --json` | — | — | self-description for any agent framework |

The top five are the **cheap loop** (zero Isabelle, runnable in CI and the model's tight
cadence). The bottom two are the **expensive loop**, where i-orca's MCP design earns its keep.

### Hiding a slow, stateful prover behind stateless-looking calls

1. **Per-step granularity is the default, not batch.** `hammer_step(source, s5)` attacks *one*
   hole, bounded by `timeout_s`, returns a reconstructed `by (metis …)` or null. Bounds each
   call's latency and keeps it **agent-legible** — one obligation, one result, next move. A
   monolithic "prove everything" call is a minutes-long opaque box; a sequence of `hammer_step`
   calls is a loop the model can reason through.
2. **Warm session reuse, invisible to the model.** The server holds a persistent Isabelle
   session with the heap from `## imports` (`Complex_Main`, `HOL-Analysis`) preloaded once, and
   routes `check`/`hammer` to it instead of cold-starting Isabelle (tens of seconds) per call.
   The LLM never knows a session exists. Single biggest usability lever; entirely server-side.
3. **The `Using` column is already in the call.** Because the source carries dependency edges,
   `hammer_step` hands Sledgehammer its relevance hints for free — the same annotation the
   static verifier reads as the DAG.

### Structured errors are prompt fragments, not log lines

`check_proof` returning a failed obligation:

```json
{ "formal_fraction": 0.71,
  "steps": {"s2":"checked","s3":"checked","s5":"failed"},
  "open_obligations": [
    { "step":"s5", "goal":"even q",
      "fixed":["p","q","k"], "assume":["q ≠ 0","sqrt 2 = p/q","coprime p q"],
      "using":["s1","s4"], "by":"substitute, even_sq_even",
      "suggestion":"hammer_step(s5) with using=[s1,s4]" } ] }
```

That object drops straight into the next generation turn — goal, local context, facts in
scope, the model's own prior informal reason. No parsing Isabelle's stderr, no temp `.thy`, no
shell. The server absorbs heap management, ATP installs, PIDE/`isabelle process` orchestration,
and result parsing — the brittle glue that otherwise kills agent reliability.

### The autonomous loop

```
generate .i.orca.md → verify_proof (cheap) → refine_proof until valid
   → compile_proof isar → check_proof (warm session)
   → for each open obligation: hammer_step → on fail, refine that step
   → repeat until formal_fraction → 1.0
   → exports: compile_proof tex (always) | compile_proof lean4 (best-effort)
```

Because every leg is a structured call with structured feedback, an agent can drive this with
no human — the i-orca analog of n-orca's autonomous improvement scheduler — climbing
`formal_fraction` toward 1.0.

**Graceful degradation (mirrors q-orca's optional QuTiP):** `parse`/`verify`/`compile` need
zero Isabelle; only `check`/`hammer` bind to the warm session. CI and the fast refine loop run
without the heavy dependency.

---

## 8. Metrics

i-orca carries the family's verifier-vs-backend metric natively (full cross-family definition
in [`docs/verifier-backend-metrics.md`](docs/verifier-backend-metrics.md)):

- `formal_fraction_static` — from `verify_proof`, no Isabelle: fraction of steps with a
  concrete method (vs `hammer`/`sorry`/`sketched`). A coverage *estimate*.
- `formal_fraction_real` — from `check_proof`: fraction of steps Isabelle's kernel **accepts**.
  The agreement-corrected truth.
- `sledgehammer_success_rate` — `hammer` holes auto-discharged / total holes.

The gap `formal_fraction_static − formal_fraction_real` is exactly the static-vs-ground-truth
disagreement the cross-family metric measures, in miniature.

---

## 9. Code structure & family conventions

```
i-orca/
  i_orca/
    ast.py            # Theorem, Imports, Context, Goal, Step, Block(case|induction), Scope
    parser/           # markdown tables → AST
    verifier/         # structural.py · scope.py · cases.py · discharge.py · naming.py
    compiler/
      isar.py         # PRIMARY → .thy
      tex.py          # always-emits LaTeX
      lean4.py        # best-effort skeleton export
    backend/          # isabelle runner: warm session, Sledgehammer orchestration, result parse
    cli.py · mcp_server.py
  examples/ *.i.orca.md (+ .thy)
  docs/  grammar.md · mcp.md · verifier-backend-metrics.md
  .claude/skills/  i-orca-verify · i-orca-compile · i-orca-prove
  openspec/         # spec-driven changes (family convention)
  AGENTS.md · README.md · SPEC.md
```

Python 3.12, pytest + ruff, OpenSpec-driven, MCP server, `.i.orca.md` extension — same shape as
`n-orca`/`q-orca`.

---

## 10. Where it sits in the research program

A Pillar-1 family **sibling** (extends the verifiable-language philosophy into formal math),
**not** an SAE-pipeline stage. The non-forced integration hook: the program currently *asserts*
several theorems only numerically — sm-sae's anomaly cancellation (~1e-15) and the 7-dim
incidence null space, econ's accounting identities (~1e-13), polygram's closed-form interference
`|⟨A|B⟩|² = M + V·cos δ`. i-orca turning those internal-consistency checks from *asserted* into
*kernel-verified* is "verify before you trust," extended to the program's own theorems. **Isar
is a better fit than Lean for this program specifically**: the claims are analysis / linear-algebra
flavored, and Isabelle's `HOL-Analysis` + Sledgehammer over reals/complex is one of its strongest
areas.

---

## 11. Honest reckonings

1. **The "just write Isar" falsifier (headline experiment).** Because the i-orca→Isar gap is so
   small, the marginal value over emitting Isar directly is thin. The whole bet reduces to one
   measurable claim: *do LLMs produce valid `.i.orca.md` tables more reliably than valid Isar
   surface syntax?* Isar is already fairly LLM-friendly (more than Lean tactic mode). If the
   answer is "about the same," i-orca collapses to "a linter + relevance-hint extractor for
   Isar" — still useful, much less grand. **This is the experiment that decides whether i-orca
   is a contribution or a wrapper, and it's runnable on day one.**
2. **The static layer is latency, not capability.** It catches nothing Isabelle wouldn't; its
   value is the fast, Isabelle-free refine loop and stable codes. Do not oversell it as a new
   guarantee.
3. **The informal-move wall is Isar's wall, relocated.** "By symmetry," "WLOG," "the other
   cases are similar" are exactly what LLM proofs lean on and exactly what doesn't lower cleanly.
   Isar has `wlog`/symmetry tooling but it's nontrivial. The "intermediate register" promise is
   bounded by what Isar can express; the genuinely-informal steps stay `sorry`.
4. **Lean 4 export is structure-only, full stop.** Methods don't transfer; library names differ.
   Frame it as cross-prover skeleton portability for exploration, never as proof transfer.
5. **The disclaimer in §2 is load-bearing.** A structurally-valid i-orca proof can be false and
   looks authoritative. Every surface (CLI, MCP, TeX) must distinguish *structurally well-formed*
   from *kernel-proved*. The danger is worse than Orca's (an unimplemented action is obviously
   incomplete; a false proof is not).
6. **Isabelle is a heavy operational dependency.** No `pip install`; needs the Isabelle
   distribution + ATPs for Sledgehammer. Mitigated by graceful degradation (§7) — but the
   `check`/`hammer` path is genuinely harder to deploy than any other dialect's backend.

---

## 12. Prior art (positioned honestly)

This neighborhood is occupied; the novelty is narrow and should be claimed narrowly.

- **Isabelle/Isar** — the structured-readable declarative register; i-orca is, frankly, *Isar in
  Markdown tables with an LLM-native surface*.
- **Draft-Sketch-Prove** (Jiang et al.) — *literally* "LLM writes informal sketch → formal
  skeleton with holes → hammer fills holes." i-orca is a typed DSL for that pattern.
- **Mizar**, **Naproche/ForTheL** (controlled NL → checkable), **LeanDojo / autoformalization** —
  overlapping.

i-orca's actual contribution: (1) the Markdown-table / LLM-native register (LLMs emit tables
reliably — the Orca bet), (2) a standalone static structural verifier with stable codes as a
cheap pre-prover filter, separable from any prover, (3) dual TeX + Lean export from one source
of truth, (4) the MCP surface that hides a slow stateful prover behind stateless-looking
per-step calls, and (5) fitting the family's verify-before-execute discipline. Not "a new way to
formalize mathematics."
