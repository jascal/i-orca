<!--
  Complexity-of-irreducibility investigation (branch complexity/irreducibility-hardness).
  This i-orca file exercises the toolchain on the subtree with a concrete witness;
  the abstract development (margin reformulation, single_competitor_reducible, and
  the Route A/B targets) lives in Hardness.thy. See PROPOSAL.md.
-->

# theorem SingleCompetitorReducibleWitness
> Route B base case, concrete witness. With a single competitor (outcome 1), the token t = 0 decided by the full source set {1,2} is ALSO decided by the singleton {1} — hence reducible. This illustrates `single_competitor_reducible` in Hardness.thy: irreducibility requires at least two competitors. (Deciding = the t-sum strictly exceeds every competitor-sum.)

## imports
| Theory       |
|--------------|
| Complex_Main |

## context
| Name   | Statement |
|--------|-----------|
| cc_def | ⋀j v. cc (j::nat) (v::nat) = (if v = 0 then (if j = 1 then (2::real) else 1) else 0) |

## goal
| Statement |
|-----------|
| (∑j∈{1,2}. cc j 1) < (∑j∈{1,2}. cc j 0) ∧ (∑j∈{1::nat}. cc j 1) < (∑j∈{1}. cc j 0) |

## proof
| Id     | Claim | By | Using | Method | Status |
|--------|-------|----|-------|--------|--------|
| s_full | (∑j∈{1,2}. cc j 1) < (∑j∈{1,2}. cc j 0) | the full pair decides t = 0 | — | (simp add: cc_def) | method |
| s_sing | (∑j∈{1::nat}. cc j 1) < (∑j∈{1}. cc j 0) | yet the singleton {1} already decides it | — | (simp add: cc_def) | method |
| s_show | (∑j∈{1,2}. cc j 1) < (∑j∈{1,2}. cc j 0) ∧ (∑j∈{1::nat}. cc j 1) < (∑j∈{1}. cc j 0) | so this full-deciding token is reducible | s_full, s_sing | simp | method |
