# Erdős #1144: completed stationary candidate proof

Status: **proved in Lean**, 2026-09-06.

The requested outcome was the full Erdős #1144 formalization, with no
unproved analytic premise or proof placeholder in the final theorem. This
is now achieved. `Erdos.Problem1144.erdos1144` builds and its fresh axiom
audit is exactly:

```text
[propext, Classical.choice, Quot.sound]
```

The final proof is in `Erdos/Problem1144/Final.lean`. Its input is the proved
`candidate_scheduledGaussianRobustCrossing_certificate` in
`HarperCandidateFinalCertificate.lean`; it no longer uses
`harperThresholdAbundanceCertificate`.

## Statement and model

`Targets.lean` defines the conclusion as

```lean
∀ᵐ omega ∂mu, ∀ A : ℝ, ∃ᶠ N : ℕ in atTop, A ≤ normSum omega N
```

Here `normSum omega N = S omega (N+1) / sqrt(N+1)`, so every positive integer
cutoff is covered. `Statistics.lean` sums `f` over `Icc 1 N`; `Model.lean`
defines `f` by the parity of prime valuations under independent fair prime
signs. This is the complete multiplicative model, not the auxiliary
squarefree process. The conclusion is positive unboundedness arbitrarily
late, with a common almost-sure event for every real threshold. It matches
conclusion (T) in the original proof candidate.

## Final mathematical assembly

1. **Actual screened squarefree crossing.** The proved near/far moments give
   a common covariance-degree event with failure tending to zero. Its bound
   is uniform over every grid cardinality `n <= T`, independently of the
   outer schedule. The actual retained variance floor has a fixed positive
   probability, and common mesh, screen-deletion and Perron losses vanish.
   Selected cardinality `>= 2*T^(9/10)` pays for degree `floor(T^(4/5))`
   and the Gaussian size test. Endpoint:
   `candidate_exists_squarefreeWhite_linear_grid_crossing`.

2. **Correct smaller time.** Set `W(T)=kappa*loglog(T)` and `V=T/W(T)`.
   Keep the original `Fin(candidateScheduleM kappa T)` coordinates and
   selected set, translating the affine grid to start at `alpha*V`.
   The original cardinality is at most `V`, its retained subset exceeds
   `2*V^(9/10)`, and the translated points lie in `[alpha*V,beta*V]`.
   Logarithmic comparisons between `T` and `V` are proved, including the
   exact integer rounding and original block width.

3. **Complete/squarefree stationary comparison.** Three actual positive
   semidefinite covariance comparisons, two exact decompositions, diagonal
   Gaussian scaling and reflection give

   ```text
   squarefree-white crossing / 8
     <= complete-white crossing + high-frequency tail / 4
        + stationary-extension tail / 2.
   ```

   Every selector is preserved. Both tails are literal Gaussian covariance
   laws. All measurability, integrability, exceptional null sets and
   conditional Gaussian identifications are proved. The exact required
   squarefree threshold is bounded by a fixed multiple of
   `log(1+log V)^8`, already supplied by the squarefree lower bound.
   Endpoints:
   `candidate_exists_stationary_squarefree_selected_lower` and
   `candidate_exists_integral_squarefree_complete_white_comparison`.

4. **Both Gaussian tails vanish uniformly.** The spectral cutoff is
   `(log T)^2`; its averaged maximum tail tends to zero uniformly over all
   original-size grids. The complete stationary extension uses the proved
   fractional energy moment and requires `2 < (alpha-1)*kappa`.
   The actual tail laws, Gaussian realizations and probability integrals
   are instantiated by `StationaryGaussianTails` and
   `StationaryGaussianTailRates`.

5. **Literal final field.** `ScheduledCompleteWhite` obtains positive
   complete-white crossings on each original block/shift with the actual
   old-negative selector. `ScheduledPrimeLaw` identifies the complete
   coefficients, prefix floors, whole-bin prime deletion and finite
   Gaussian product law with `candidateScheduledGaussianFresh`.
   `ScheduledWhiteAssembly` then supplies the robust Gaussian certificate.

The concrete witness is

```text
alpha = 7/6, beta = 5/4, kappa = 18, rho = 1/2,
(alpha - 1)*kappa = 3 > 2.
```

The positive crossing mass is supplied existentially by the proved lower
bound. All inequalities on the fixed parameters are checked in Lean. The
previously proved cylinder, sign-replacement and schedule reductions then
yield the unconditional `erdos1144` theorem.

## Verification

- Full build: `lake build Erdos.Problem1144` passed **8917 jobs**.
- All **294 candidate modules** are reachable from the umbrella.
- This final pass added **25 modules**, with **71 public declarations**:
  62 theorems and nine definitions. Every declaration was individually
  audited to standard axioms only. These new source modules contain no
  `sorry` or added axiom.
- The instantiated certificate was built and audited before `Final.lean`
  was changed. A subsequent full build and fresh final-theorem audit passed.
- The target/model definitions were independently checked against the
  original candidate, including the complete model, normalization and
  positive/frequent quantifiers.

Reusable verification source:
`notes/1144/experiments/candidate_final_certificate_axioms.lean`.
It can be run with `lake env lean` after the full build.

The original development build and audits above preceded publication. The
standalone release's build and audit evidence is recorded in
[verification/README.md](../../verification/README.md), with the actual
endpoint report in [axiom-audit.txt](../../verification/axiom-audit.txt).

Final source SHA-256:
`050185c8c46797459f13480f8ca098e079670fb5df616cccea2a22b7c3ef680c`.

Historical alternative-route axioms and conditional theorems remain
preserved. They are not dependencies of `erdos1144`; the fresh kernel
axiom report establishes that independence. No active proof obligation
remains. The proof reuses analytic infrastructure from the associated
[Erdős #520 development](https://github.com/saasom/Erdos520).
