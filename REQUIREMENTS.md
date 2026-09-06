# Verification requirements

Required tools are Git and Elan, the Lean toolchain manager. Python 3 is used
only to check the text of the axiom reports; the mathematical proof itself
is checked by Lean. Internet access is needed for the initial dependency and
Mathlib cache downloads.

The compiler is pinned in `lean-toolchain`:

```text
leanprover/lean4:v4.30.0-rc2
```

Mathlib is pinned to commit `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
All transitive package revisions are recorded in `lake-manifest.json`.
No unrecorded Mathlib source patch is required.

Install Elan using the official Lean setup instructions, then run from the
repository root:

```sh
lake exe cache get
lake build
lake env lean Audit.lean | tee axiom-audit.txt
python3 scripts/check_axioms.py axiom-audit.txt
```

The final command verifies that the certificate and final theorem both
depend on exactly `propext`, `Classical.choice`, and `Quot.sound`.

The dependency cache and compiled proof require disk space beyond the source
checkout. Building the proof is CPU-intensive. No external theorem prover
or numerical oracle is required.
