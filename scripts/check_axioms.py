#!/usr/bin/env python3
"""Check the actual Lean reports for the two public release endpoints."""

from pathlib import Path
import re
import sys

EXPECTED = {
    "Erdos.Problem1144.candidate_scheduledGaussianRobustCrossing_certificate",
    "Erdos.Problem1144.erdos1144",
}
STANDARD = {"propext", "Classical.choice", "Quot.sound"}


def check(text: str) -> None:
    if re.search(r"\berror:|\bsorryAx\b", text):
        raise ValueError("Lean reported an error or an unfinished proof")
    reports = re.findall(
        r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]", text, re.S
    )
    if len(reports) != len(EXPECTED) or {name for name, _ in reports} != EXPECTED:
        raise ValueError("Missing, duplicate, or unexpected endpoint axiom report")
    for name, axes in reports:
        actual = {item.strip() for item in axes.split(",") if item.strip()}
        if actual != STANDARD:
            raise ValueError(f"Unexpected axioms for {name}: {sorted(actual)}")


if __name__ == "__main__":
    check(Path(sys.argv[1]).read_text())
    print("Both public endpoints use exactly Lean's three standard axioms.")
