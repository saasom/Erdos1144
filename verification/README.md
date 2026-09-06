# Verification record

The standalone release package was built and audited on 6 September 2026.
The endpoint audit and source-hash checks had passed by 09:32:34 UTC.

## Standalone build

`lake build` completed successfully: **8919 jobs**. This build started with
no project build directory. It rebuilt the packaged project sources while
reusing the existing cache for the pinned external dependencies.

- Lean: `leanprover/lean4:v4.30.0-rc2`.
- Mathlib commit: `5450b53e5ddc75d46418fabb605edbf36bd0beb6`.
- Local source closure: **605 unchanged Lean modules, 207,626 lines**.
- All 605 entries in [source-snapshot.sha256](source-snapshot.sha256) passed
  SHA-256 verification against the source package that was built.

The full development proof had already passed its own build and declaration
audits. This additional build checks the separately packaged release.

## Actual endpoint audit

[axiom-audit.txt](axiom-audit.txt) is the unedited output of
`lake env lean Audit.lean` in the standalone package. Lean exited successfully,
and `scripts/check_axioms.py` accepted the report. Both
`candidate_scheduledGaussianRobustCrossing_certificate` and `erdos1144`
depend exactly on:

```text
[propext, Classical.choice, Quot.sound]
```

The report also checks that the public theorem has type
`Erdos.Problem1144.Erdos1144`, without hypotheses.

The local report includes a Lake warning about changes in the shared Mathlib
checkout. Those changes are six deleted files under `scripts/bench/build/`;
no tracked Lean source was changed. The release pins the upstream commit,
and GitHub Actions obtains its own dependency checkout.

Historical alternative-route axioms and vendored blueprint placeholder
tooling remain in the unchanged source snapshot. They are not dependencies
of either audited endpoint. The claim established here is the absence of
unproved assumptions from the public theorem and its actual certificate.

## Reproduce

From the repository root, with Git, Elan and Python 3 installed:

```sh
sha256sum --check verification/source-snapshot.sha256
lake exe cache get
lake build
lake env lean Audit.lean | tee axiom-audit.txt
python3 scripts/check_axioms.py axiom-audit.txt
```

On macOS, use `shasum -a 256 -c verification/source-snapshot.sha256` for the
first command. The [GitHub Actions workflow](../.github/workflows/verify.yml)
repeats the source-hash check, build and endpoint audit, and preserves the
new audit output as an artifact. Its result is reported separately on the
[Actions page](https://github.com/saasom/Erdos1144/actions/workflows/verify.yml).

The final theorem source has SHA-256
`050185c8c46797459f13480f8ca098e079670fb5df616cccea2a22b7c3ef680c`.
