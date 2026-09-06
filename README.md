# Erdős Problem #1144 — proved in Lean 4

[![Verify Lean proof](https://github.com/saasom/Erdos1144/actions/workflows/verify.yml/badge.svg)](https://github.com/saasom/Erdos1144/actions/workflows/verify.yml)

**Human-readable proof:** [Web writeup](paper/erdos1144_proof_candidate.md) ·
[Typeset PDF](paper/erdos1144_proof_candidate.pdf)

This repository contains a kernel-checked Lean 4 proof of the positive
unboundedness assertion in [Erdős Problem #1144](https://www.erdosproblems.com/1144).
Independently assign a fair sign to every prime and extend the signs
**completely multiplicatively**. Writing `S(N) = Σ_{n ≤ N} f(n)`, the result is

```text
almost surely, limsup_{N → ∞} S(N) / sqrt(N) = +∞.
```

The public theorem has no hypotheses and depends exactly on Lean's standard
foundations: `propext`, `Classical.choice`, and `Quot.sound`. No `sorry` or
unproved analytic axiom is a dependency of this theorem.

## Public theorem

[`Erdos/Problem1144/Final.lean`](Erdos/Problem1144/Final.lean) proves

```lean
theorem erdos1144 : Erdos1144
```

The target in [`Targets.lean`](Erdos/Problem1144/Targets.lean) is

```lean
∀ᵐ omega ∂mu, ∀ A : ℝ, ∃ᶠ N : ℕ in atTop, A ≤ normSum omega N
```

Here `normSum omega N = S omega (N+1) / sqrt(N+1)`. The index shift covers
every positive integer cutoff. The conclusion gives arbitrarily late
**positive** crossings above every real threshold, on a single almost-sure
event.

## Check the statement and model

- [`Model.lean`](Erdos/Problem1144/Model.lean) constructs the infinite product
  of fair signs and defines the complete multiplicative function by parity
  of prime valuations.
- [`Statistics.lean`](Erdos/Problem1144/Statistics.lean) defines `S` as the sum
  over the integers from `1` through `N`.
- [`Targets.lean`](Erdos/Problem1144/Targets.lean) defines the normalization and
  the almost-sure, arbitrarily-late conclusion.
- [`HarperCandidateFinalCertificate.lean`](Erdos/Problem1144/HarperCandidateFinalCertificate.lean)
  instantiates the actual fresh-prime Gaussian certificate.
- [`Final.lean`](Erdos/Problem1144/Final.lean) applies the proved reductions to
  that certificate.

The auxiliary squarefree process is used inside the proof. The public
conclusion concerns the complete multiplicative model.

## Reproduce the build and trust audit

The project pins Lean and Mathlib to `v4.30.0-rc2`; `lake-manifest.json`
records all resolved package commits. With Git and Elan installed, run:

```sh
lake exe cache get
lake build
lake env lean Audit.lean | tee axiom-audit.txt
python3 scripts/check_axioms.py axiom-audit.txt
```

[`Audit.lean`](Audit.lean) prints the dependencies of the instantiated
certificate and `erdos1144`. Both reports must contain exactly

```text
[propext, Classical.choice, Quot.sound]
```

GitHub Actions builds the packaged sources and checks these actual axiom
reports on pushes and pull requests. Linter warnings do not indicate an
unfinished proof. See [REQUIREMENTS.md](REQUIREMENTS.md) and the
[verification record](verification/README.md).

Historical conditional interfaces and alternative-route axioms remain in
some source files, and vendored blueprint tooling includes a placeholder
tactic. They are preserved with the original sources. Neither the final
theorem nor its instantiated certificate depends on an unproved assumption;
the endpoint axiom reports are the check for this claim.

## Proof route

1. Prove a selected squarefree white Gaussian crossing using the actual
   screened covariance-degree bound, variance floor, and Gaussian thinning.
2. Transfer this bound at the smaller time `V = T / (κ log log T)`, keeping
   the original grid cardinality and selected set.
3. Compare the squarefree and complete stationary covariances, with exact
   Gaussian normalization and both omitted-component tails.
4. Prove that the high-frequency and complete stationary-extension tails
   vanish uniformly over the actual scheduled grids.
5. Identify the complete white and actual fresh-prime Gaussian laws, then
   apply the cylinder, sign-replacement and schedule reductions.

The fixed certificate uses `α = 7/6`, `β = 5/4`, `κ = 18`, and `ρ = 1/2`.
In particular, `(α−1)κ = 3 > 2`, as required by the proved extension-tail
bound. All analytic inputs to the final theorem are proved in Lean.

The [completed proof guide](notes/1144/complete_proof.md) describes the exact
interfaces. The [original informal candidate](paper/erdos1144_proof_candidate.md)
is retained as a dated exposition from 5 September 2026, with corrected
math rendering and a [typeset PDF](paper/erdos1144_proof_candidate.pdf).
Its mathematical claims are unchanged. The formalization completed on
6 September is authoritative for the checked result; no line-by-line
correspondence between the exposition and Lean is claimed. Its analytic
inputs are proved in Lean, as described in the completed proof guide.

## Sources, attribution and citation

This release packages 605 local Lean modules (207,626 lines), copied
unchanged from the verified development, together with their pinned
dependencies and third-party notices. The original module hashes are
recorded in [verification/source-snapshot.sha256](verification/source-snapshot.sha256).

The proof reuses and extends analytic infrastructure developed for
[Erdős #520](https://github.com/saasom/Erdos520), including Harper moment,
Euler-product, prime and Gaussian comparison machinery. Vendored prime
number theorem, sieve and blueprint sources retain their upstream notices.
See [THIRD_PARTY_NOTICES.md](THIRD_PARTY_NOTICES.md).

Citation metadata are in [CITATION.cff](CITATION.cff). The original development
is released under the [Apache License 2.0](LICENSE). The
[v1.0.0 release](https://github.com/saasom/Erdos1144/releases/tag/v1.0.0)
and its Git commit identify this public source snapshot.
