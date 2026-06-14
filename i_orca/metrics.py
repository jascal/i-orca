"""Verifier-vs-backend metrics (SPEC §8).

Three numbers organise i-orca's honesty about the gap between *structurally
well-formed* and *kernel-proved*:

* ``formal_fraction_static`` — fraction of steps with a concrete Isar method
  (not ``hammer``/``sorry``/``sketched``). A coverage *estimate*, computed with
  zero Isabelle.
* ``formal_fraction_real`` — fraction of steps Isabelle's kernel accepts
  (status ``checked``). Populated only by a backend run; ``None`` until then.
* ``sledgehammer_success_rate`` — ``hammer`` holes auto-discharged / total holes.

The gap ``formal_fraction_static − formal_fraction_real`` is the static-vs-
ground-truth disagreement the cross-family metric measures, in miniature.
"""
from __future__ import annotations

from dataclasses import dataclass, field

from i_orca.ast import Theorem


@dataclass
class ProofMetrics:
    n_steps: int = 0
    n_method: int = 0          # concrete method, expected to check
    n_hammer: int = 0          # structured hole marked for Sledgehammer
    n_sketched: int = 0        # prose-only / sorry hole
    n_checked: int = 0         # kernel-confirmed (backend only)
    n_failed: int = 0          # method present but kernel rejected (backend only)
    status_counts: dict[str, int] = field(default_factory=dict)

    @property
    def n_frontier(self) -> int:
        """Holes on the formalization frontier (hammer + sketched)."""
        return self.n_hammer + self.n_sketched

    @property
    def formal_fraction_static(self) -> float:
        if self.n_steps == 0:
            return 1.0
        return self.n_method / self.n_steps

    @property
    def formal_fraction_real(self) -> float | None:
        """Only meaningful once a backend run has populated ``checked``/``failed``."""
        if self.n_checked == 0 and self.n_failed == 0:
            return None
        if self.n_steps == 0:
            return 1.0
        return self.n_checked / self.n_steps

    @property
    def sledgehammer_success_rate(self) -> float | None:
        total_holes = self.n_hammer + self.n_checked  # checked holes were hammered
        if total_holes == 0:
            return None
        return self.n_checked / total_holes

    def to_dict(self) -> dict:
        out = {
            "n_steps": self.n_steps,
            "n_method": self.n_method,
            "n_hammer": self.n_hammer,
            "n_sketched": self.n_sketched,
            "n_frontier": self.n_frontier,
            "formal_fraction_static": round(self.formal_fraction_static, 4),
            "status_counts": dict(self.status_counts),
        }
        real = self.formal_fraction_real
        if real is not None:
            out["formal_fraction_real"] = round(real, 4)
            out["n_checked"] = self.n_checked
            out["n_failed"] = self.n_failed
        rate = self.sledgehammer_success_rate
        if rate is not None:
            out["sledgehammer_success_rate"] = round(rate, 4)
        return out


def compute_metrics(theorem: Theorem) -> ProofMetrics:
    """Tally a theorem's steps into a :class:`ProofMetrics` (zero Isabelle)."""
    m = ProofMetrics()
    for step in theorem.proof.steps():
        m.n_steps += 1
        st = step.static_status
        m.status_counts[st] = m.status_counts.get(st, 0) + 1
        if st == "method":
            m.n_method += 1
        elif st == "hammer":
            m.n_hammer += 1
        elif st == "sketched":
            m.n_sketched += 1
        elif st == "checked":
            m.n_checked += 1
            m.n_method += 1  # a checked step is also formal
        elif st == "failed":
            m.n_failed += 1
    return m
