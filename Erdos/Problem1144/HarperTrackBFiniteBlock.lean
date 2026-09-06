import Erdos.Problem1144.HarperTrackB
import Erdos.Problem1144.HarperShortMemoryCovariance
import Erdos.Problem1144.HarperTrackBPrefixMartingaleCLT
import Erdos.Problem1144.HarperProcess

open MeasureTheory Filter
open scoped BigOperators ENNReal Topology

namespace Erdos
namespace Problem1144

/-!
# Track B finite core block interface

This file records the current finite, quantitative Track B target.

The analytic proof of a squarefree Brownian block is now organized around the
short-memory decomposition

```text
Z_r = Y_r + B_r + Z_r^flat,
```

where:

* `Y_r` is the rough-prime core with exactly diagonal conditional covariance;
* `B_r` is the two-sided boundary piece with small covariance row sum;
* `Z_r^flat` is the Rankin-discarded part whose small-prime component is too
  large.

Before applying the prefix-vector martingale CLT replacement, the core is also
degree truncated:

```text
Y_r -> Y_r^(<=D).
```

The six named inputs are kept visible as separate error budgets:

1. product/diagonal lower event (`errProduct`);
2. boundary Markov event (`errBoundary`);
3. flat Rankin/Menshov event (`errFlat`);
4. degree-cutoff Rankin/Menshov event (`errDegree`);
5. rough-core prefix martingale replacement (`errMOO`, legacy field name);
6. Gaussian crossing with polynomial variance-ratio loss (`errGaussian`).

The final theorem wiring is deliberately unchanged.  This module only proves
that such a finite-core block certificate feeds the already formalized fixed
base Track B transfer.
-/

/-!
## Squarefree weighted second moments

The flat and degree tails in Track B are squarefree-supported finite weighted
sums.  The next lemmas isolate the exact orthogonality calculation they need.
-/

/-- Finite weighted sum of the squarefree-supported model. -/
noncomputable def squarefreeWeightedSum
    (S : Finset ℕ) (w : ℕ → ℝ) (omega : Omega) : ℝ :=
  ∑ n ∈ S, w n * gSquarefree omega n

/-- Products of two squarefree-supported model values are integrable. -/
theorem integrable_gSquarefree_mul_gSquarefree (a b : ℕ) :
    Integrable
      (fun omega : Omega => gSquarefree omega a * gSquarefree omega b) mu := by
  by_cases ha : Squarefree a <;> by_cases hb : Squarefree b
  · simpa [gSquarefree, ha, hb] using integrable_f_mul_f a b
  · simp [gSquarefree, hb]
  · simp [gSquarefree, ha]
  · simp [gSquarefree, ha, hb]

/-- Squarefree-supported model values are integrable. -/
theorem integrable_gSquarefree (n : ℕ) :
    Integrable (fun omega : Omega => gSquarefree omega n) mu := by
  refine
    (integrable_gSquarefree_mul_gSquarefree n 1).congr
      (ae_of_all _ ?_)
  intro omega
  simp [gSquarefree]

/-- Two-point orthogonality for the squarefree-supported model. -/
theorem integral_gSquarefree_mul_gSquarefree_eq
    {a b : ℕ} (ha_pos : 0 < a) (hb_pos : 0 < b) :
    ∫ omega, gSquarefree omega a * gSquarefree omega b ∂mu =
      (if Squarefree a ∧ Squarefree b then squareIndicator (a * b) else 0) := by
  by_cases ha : Squarefree a <;> by_cases hb : Squarefree b
  · simp [gSquarefree, ha, hb, integral_f_mul_f_eq_squareIndicator ha_pos hb_pos]
  · simp [gSquarefree, hb]
  · simp [gSquarefree, ha]
  · simp [gSquarefree, ha, hb]

/-- One-point expectation for the squarefree-supported model. -/
theorem integral_gSquarefree_eq
    {n : ℕ} (hn_pos : 0 < n) :
    ∫ omega, gSquarefree omega n ∂mu =
      (if Squarefree n then squareIndicator n else 0) := by
  calc
    ∫ omega, gSquarefree omega n ∂mu
        =
      ∫ omega, gSquarefree omega n * gSquarefree omega 1 ∂mu := by
        congr 1
        funext omega
        simp [gSquarefree]
    _ = (if Squarefree n ∧ Squarefree 1 then squareIndicator (n * 1) else 0) :=
        integral_gSquarefree_mul_gSquarefree_eq hn_pos (by norm_num)
    _ = (if Squarefree n then squareIndicator n else 0) := by
        simp

/-- Squared finite squarefree-weighted sums are integrable. -/
theorem integrable_squarefreeWeightedSum_sq
    (S : Finset ℕ) (w : ℕ → ℝ) :
    Integrable (fun omega : Omega => (squarefreeWeightedSum S w omega) ^ 2) mu := by
  classical
  unfold squarefreeWeightedSum
  simp_rw [pow_two, Finset.sum_mul_sum]
  exact
    integrable_finset_sum S fun a _ha =>
      integrable_finset_sum S fun b _hb =>
        ((integrable_gSquarefree_mul_gSquarefree a b).const_mul (w a * w b)).congr
          (ae_of_all _ fun omega => by ring)

/-- Exact second moment of a finite squarefree-weighted sum. -/
theorem integral_squarefreeWeightedSum_sq_eq
    (S : Finset ℕ) (w : ℕ → ℝ)
    (hpos : ∀ n, n ∈ S → 0 < n) :
    ∫ omega, (squarefreeWeightedSum S w omega) ^ 2 ∂mu =
      ∑ a ∈ S, ∑ b ∈ S,
        w a * w b *
          (if Squarefree a ∧ Squarefree b then squareIndicator (a * b) else 0) := by
  classical
  unfold squarefreeWeightedSum
  simp_rw [pow_two, Finset.sum_mul_sum]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro a ha
    rw [integral_finset_sum]
    · refine Finset.sum_congr rfl ?_
      intro b hb
      have ha_pos : 0 < a := hpos a ha
      have hb_pos : 0 < b := hpos b hb
      calc
        ∫ omega, (w a * gSquarefree omega a) * (w b * gSquarefree omega b) ∂mu
            =
          w a * w b *
            ∫ omega, gSquarefree omega a * gSquarefree omega b ∂mu := by
              rw [← integral_const_mul]
              congr 1
              funext omega
              ring
        _ =
          w a * w b *
            (if Squarefree a ∧ Squarefree b then squareIndicator (a * b) else 0) := by
              rw [integral_gSquarefree_mul_gSquarefree_eq ha_pos hb_pos]
    · intro b _hb
      exact
        ((integrable_gSquarefree_mul_gSquarefree a b).const_mul
          (w a * w b)).congr
          (ae_of_all _ fun omega => by ring)
  · intro a _ha
    exact
      integrable_finset_sum S fun b _hb =>
        ((integrable_gSquarefree_mul_gSquarefree a b).const_mul
          (w a * w b)).congr
          (ae_of_all _ fun omega => by ring)

/-- For positive squarefree integers, a square product forces equality. -/
theorem eq_of_squarefree_mul_isSquare
    {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (_ha_pos : 0 < a) (_hb_pos : 0 < b)
    (hsq : IsSquare (a * b)) :
    a = b := by
  have h :=
    squarefree_parts_eq_of_mul_square
      (a := a) (b := b) (da := a) (db := b) (ua := 1) (ub := 1)
      (by norm_num) (by norm_num) ha hb (by simp) (by simp) hsq
  exact h

/-- On positive squarefree pairs, the square indicator is the diagonal
indicator. -/
theorem squareIndicator_mul_squarefree_eq_ite
    {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (ha_pos : 0 < a) (hb_pos : 0 < b) :
    squareIndicator (a * b) = if a = b then 1 else 0 := by
  classical
  rw [squareIndicator]
  by_cases hsq : IsSquare (a * b)
  · rw [if_pos hsq,
      if_pos (eq_of_squarefree_mul_isSquare ha hb ha_pos hb_pos hsq)]
  · have hne : a ≠ b := by
      intro hab
      apply hsq
      subst hab
      exact ⟨a, by ring⟩
    rw [if_neg hsq, if_neg hne]

/-- Nontrivial squarefree-supported model values have mean zero. -/
theorem integral_gSquarefree_eq_zero_of_one_lt
    {n : ℕ} (hn : 1 < n) :
    ∫ omega, gSquarefree omega n ∂mu = 0 := by
  have hn_pos : 0 < n := Nat.zero_lt_of_lt hn
  have hn_ne : n ≠ 1 := ne_of_gt hn
  rw [integral_gSquarefree_eq hn_pos]
  by_cases hsf : Squarefree n
  · have hsq :
        squareIndicator (n * 1) = if n = 1 then 1 else 0 :=
      squareIndicator_mul_squarefree_eq_ite hsf (by norm_num) hn_pos
        (by norm_num)
    simpa [hsf, hn_ne] using hsq
  · simp [hsf]

/-- Finite weighted sums supported on integers larger than one have mean zero. -/
theorem integral_squarefreeWeightedSum_eq_zero
    (S : Finset ℕ) (w : ℕ → ℝ)
    (hgt : ∀ n, n ∈ S → 1 < n) :
    ∫ omega, squarefreeWeightedSum S w omega ∂mu = 0 := by
  unfold squarefreeWeightedSum
  rw [integral_finset_sum]
  · simp_rw [integral_const_mul]
    exact Finset.sum_eq_zero fun n hn => by
      simp [integral_gSquarefree_eq_zero_of_one_lt (hgt n hn)]
  · intro n _hn
    exact (integrable_gSquarefree n).const_mul (w n)

/-- Exact diagonal second moment for finite weighted sums supported on
positive squarefree integers. -/
theorem integral_squarefreeWeightedSum_sq_eq_diag
    (S : Finset ℕ) (w : ℕ → ℝ)
    (hpos : ∀ n, n ∈ S → 0 < n)
    (hsf : ∀ n, n ∈ S → Squarefree n) :
    ∫ omega, (squarefreeWeightedSum S w omega) ^ 2 ∂mu =
      ∑ n ∈ S, (w n) ^ 2 := by
  classical
  rw [integral_squarefreeWeightedSum_sq_eq S w hpos]
  refine Finset.sum_congr rfl ?_
  intro a ha
  have ha_pos : 0 < a := hpos a ha
  have ha_sf : Squarefree a := hsf a ha
  calc
    ∑ b ∈ S, w a * w b *
        (if Squarefree a ∧ Squarefree b then squareIndicator (a * b) else 0)
        =
      ∑ b ∈ S, if a = b then w a * w b else 0 := by
        refine Finset.sum_congr rfl ?_
        intro b hb
        have hb_pos : 0 < b := hpos b hb
        have hb_sf : Squarefree b := hsf b hb
        rw [if_pos ⟨ha_sf, hb_sf⟩,
          squareIndicator_mul_squarefree_eq_ite ha_sf hb_sf ha_pos hb_pos]
        by_cases hab : a = b <;> simp [hab]
    _ = w a * w a := by
        rw [Finset.sum_eq_single a]
        · simp
        · intro b hb hba
          have hab : a ≠ b := fun h => hba h.symm
          simp [hab]
        · intro ha_not
          exact False.elim (ha_not ha)
    _ = (w a) ^ 2 := by
        ring

/-- Parameter functions for the amended finite Track B theorem.

The intended schedule is polynomial, e.g.

```text
Lambda_j = j,
eta_j = j^-(K+3),
M_j = j^(2K+8),
rho_j = eta_j / (j^2 log M_j),
theta_j = j^-(5K+25),
ell_j = j^(10K+100),
V_j = ell_j / Lambda_j^K.
```

The fields are not used by the elementary transfer proof itself; they make the
analytic certificate explicit and prevent the finite theorem from collapsing
back into an opaque "Brownian block" axiom.
-/
structure TrackBFiniteCoreParameters where
  K : ℕ
  Lambda : ℕ → ℝ
  ell : ℕ → ℝ
  theta : ℕ → ℝ
  rho : ℕ → ℝ
  eta : ℕ → ℝ
  V : ℕ → ℝ
  degree : ℕ → ℕ

/-- Total finite-core squarefree block failure budget. -/
noncomputable def trackBFiniteCoreBlockBudget
    (errProduct errBoundary errFlat errDegree errMOO errGaussian :
      ℕ → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  errProduct j + errBoundary j + errFlat j + errDegree j +
    errMOO j + errGaussian j

/-- Six finite bad events in the amended Track B squarefree block proof.

Index convention:

* `0`: small-prime product/diagonal event;
* `1`: boundary Markov event;
* `2`: flat Rankin/Menshov event;
* `3`: degree-cutoff Rankin/Menshov event;
* `4`: rough-core Gaussian replacement event;
* `5`: Gaussian crossing event.
-/
abbrev TrackBFiniteBadEvents := Fin 6 → ℕ → Set Omega

/-- The union of the six finite bad events for stage `j`. -/
def trackBFiniteCoreBadUnion
    (bad : TrackBFiniteBadEvents) (j : ℕ) : Set Omega :=
  ⋃ i : Fin 6, bad i j

/-- Deterministic conversion from a good-set success statement to the subset
shape consumed by the finite Track B certificate.  In the final decomposition
proof it is usually easier to show that outside all six bad events the
squarefree block succeeds; this lemma packages the contraposition. -/
theorem trackBSquarefreeBlockFailure_subset_finiteCoreBadUnion_of_success
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) (B : ℕ → ℝ)
    (bad : TrackBFiniteBadEvents)
    (hgood :
      ∀ j omega,
        omega ∉ trackBFiniteCoreBadUnion bad j →
          trackBSquarefreeBlockSuccess 0 endpoint mesh B omega j) :
    ∀ j,
      trackBSquarefreeBlockFailure 0 endpoint mesh B j ⊆
        trackBFiniteCoreBadUnion bad j := by
  intro j omega hfail
  by_contra hnotbad
  exact hfail (hgood j omega hnotbad)

/-- Six finite error functions in the same order as
`TrackBFiniteBadEvents`. -/
abbrev TrackBFiniteErrorBudget := Fin 6 → ℕ → ℝ≥0∞

/-- Indexed version of the finite-core block budget. -/
noncomputable def trackBFiniteCoreIndexedBudget
    (err : TrackBFiniteErrorBudget) (j : ℕ) : ℝ≥0∞ :=
  ∑ i : Fin 6, err i j

/-- Package the six named error functions as an indexed budget. -/
def trackBFiniteErrorBudgetOf
    (errProduct errBoundary errFlat errDegree errMOO errGaussian :
      ℕ → ℝ≥0∞) : TrackBFiniteErrorBudget
  | ⟨0, _⟩ => errProduct
  | ⟨1, _⟩ => errBoundary
  | ⟨2, _⟩ => errFlat
  | ⟨3, _⟩ => errDegree
  | ⟨4, _⟩ => errMOO
  | ⟨5, _⟩ => errGaussian

theorem trackBFiniteCoreIndexedBudget_of_named
    (errProduct errBoundary errFlat errDegree errMOO errGaussian :
      ℕ → ℝ≥0∞) (j : ℕ) :
    trackBFiniteCoreIndexedBudget
        (trackBFiniteErrorBudgetOf errProduct errBoundary errFlat errDegree
          errMOO errGaussian) j =
      trackBFiniteCoreBlockBudget errProduct errBoundary errFlat errDegree
        errMOO errGaussian j := by
  simp [trackBFiniteCoreIndexedBudget, trackBFiniteErrorBudgetOf,
    trackBFiniteCoreBlockBudget, Fin.sum_univ_six]

/-- Finite union bound for the six finite-core bad events. -/
theorem measure_trackBFiniteCoreBadUnion_le_indexedBudget
    (bad : TrackBFiniteBadEvents) (err : TrackBFiniteErrorBudget)
    (hprob : ∀ i j, mu (bad i j) ≤ err i j) (j : ℕ) :
    mu (trackBFiniteCoreBadUnion bad j) ≤
      trackBFiniteCoreIndexedBudget err j := by
  classical
  unfold trackBFiniteCoreBadUnion trackBFiniteCoreIndexedBudget
  calc
    mu (⋃ i : Fin 6, bad i j)
        ≤ ∑ i : Fin 6, mu (bad i j) := by
          rw [show (⋃ i : Fin 6, bad i j) =
              ⋃ i ∈ (Finset.univ : Finset (Fin 6)), bad i j by
            ext omega
            simp]
          simpa using
            MeasureTheory.measure_biUnion_finset_le
              (Finset.univ : Finset (Fin 6)) (fun i => bad i j)
    _ ≤ ∑ i : Fin 6, err i j :=
          Finset.sum_le_sum fun i _hi => hprob i j

/-- If squarefree block failure is contained in the finite bad-event union,
then the six analytic estimates give the squarefree block failure bound. -/
theorem measure_trackBSquarefreeBlockFailure_le_finiteCoreBudget
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) (B : ℕ → ℝ)
    (bad : TrackBFiniteBadEvents)
    (errProduct errBoundary errFlat errDegree errMOO errGaussian :
      ℕ → ℝ≥0∞)
    (hsubset :
      ∀ j,
        trackBSquarefreeBlockFailure 0 endpoint mesh B j ⊆
          trackBFiniteCoreBadUnion bad j)
    (hprob :
      ∀ i j,
        mu (bad i j) ≤
          trackBFiniteErrorBudgetOf errProduct errBoundary errFlat errDegree
            errMOO errGaussian i j)
    (j : ℕ) :
    mu (trackBSquarefreeBlockFailure 0 endpoint mesh B j) ≤
      trackBFiniteCoreBlockBudget errProduct errBoundary errFlat errDegree
        errMOO errGaussian j := by
  calc
    mu (trackBSquarefreeBlockFailure 0 endpoint mesh B j)
        ≤ mu (trackBFiniteCoreBadUnion bad j) :=
          measure_mono (hsubset j)
    _ ≤
        trackBFiniteCoreIndexedBudget
          (trackBFiniteErrorBudgetOf errProduct errBoundary errFlat errDegree
            errMOO errGaussian) j :=
          measure_trackBFiniteCoreBadUnion_le_indexedBudget bad
            (trackBFiniteErrorBudgetOf errProduct errBoundary errFlat errDegree
              errMOO errGaussian) hprob j
    _ =
        trackBFiniteCoreBlockBudget errProduct errBoundary errFlat errDegree
          errMOO errGaussian j :=
          trackBFiniteCoreIndexedBudget_of_named errProduct errBoundary
            errFlat errDegree errMOO errGaussian j

/-!
## Generic finite Markov helpers

The boundary event has the form

```text
exists r <= M, exists side in {left,right}:
  boundaryEnergy(side,r) > threshold.
```

The next definitions and theorem prove the purely probabilistic part from
pointwise first-moment bounds.  The number-theoretic work is only to supply the
expectation upper bounds.
-/

/-- Event that at least one of two mesh-indexed nonnegative energies exceeds
the stage threshold. -/
def trackBTwoSidedMeshAbove
    (mesh : ℕ → ℕ) (threshold : ℕ → ℝ)
    (W : Fin 2 → ℕ → ℕ → Omega → ℝ) (j : ℕ) : Set Omega :=
  {omega |
    ∃ side : Fin 2, ∃ r ∈ Finset.Icc 1 (mesh j),
      threshold j < W side j r omega}

/-- First-moment union-bound budget for `trackBTwoSidedMeshAbove`. -/
noncomputable def trackBTwoSidedMeshFirstMomentBudget
    (mesh : ℕ → ℕ) (threshold : ℕ → ℝ)
    (upper : Fin 2 → ℕ → ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ side : Fin 2, ∑ r ∈ Finset.Icc 1 (mesh j),
    ENNReal.ofReal (upper side j r / threshold j)

/-- One-sided Markov bound for a nonnegative real random variable using its
first moment. -/
theorem measure_nonneg_gt_le_first
    (W : Omega → ℝ) (A V : ℝ)
    (hA : 0 < A)
    (hint : Integrable W mu)
    (hnonneg : 0 ≤ᵐ[mu] W)
    (hmean : (∫ omega, W omega ∂mu) ≤ V) :
    mu {omega | A < W omega} ≤ ENNReal.ofReal (V / A) := by
  let T : Set Omega := {omega | A ≤ W omega}
  have hsubset : {omega | A < W omega} ⊆ T := by
    intro omega hlt
    exact le_of_lt (show A < W omega from hlt)
  have hmarkov :=
    mul_meas_ge_le_integral_of_nonneg (μ := mu)
      (f := W) hnonneg hint A
  have hTreal : mu.real T ≤ V / A := by
    have hmul : A * mu.real T ≤ V :=
      le_trans hmarkov hmean
    rw [le_div_iff₀ hA]
    simpa [mul_comm] using hmul
  have hEreal : mu.real {omega | A < W omega} ≤ V / A :=
    (measureReal_mono hsubset).trans hTreal
  rw [← ofReal_measureReal (μ := mu) (s := {omega | A < W omega})]
  exact ENNReal.ofReal_le_ofReal hEreal

/-- Finite Markov plus union bound for the two-sided boundary-energy shape. -/
theorem measure_trackBTwoSidedMeshAbove_le_firstMomentBudget
    (mesh : ℕ → ℕ) (threshold : ℕ → ℝ)
    (W : Fin 2 → ℕ → ℕ → Omega → ℝ)
    (upper : Fin 2 → ℕ → ℕ → ℝ)
    (hthreshold : ∀ j, 0 < threshold j)
    (hint :
      ∀ side j r, r ∈ Finset.Icc 1 (mesh j) →
        Integrable (fun omega => W side j r omega) mu)
    (hnonneg :
      ∀ side j r, r ∈ Finset.Icc 1 (mesh j) →
        0 ≤ᵐ[mu] fun omega => W side j r omega)
    (hmean :
      ∀ side j r, r ∈ Finset.Icc 1 (mesh j) →
        (∫ omega, W side j r omega ∂mu) ≤ upper side j r)
    (j : ℕ) :
    mu (trackBTwoSidedMeshAbove mesh threshold W j) ≤
      trackBTwoSidedMeshFirstMomentBudget mesh threshold upper j := by
  classical
  let s : Finset ℕ := Finset.Icc 1 (mesh j)
  let point : Fin 2 → ℕ → Set Omega := fun side r =>
    {omega | threshold j < W side j r omega}
  have hrewrite :
      trackBTwoSidedMeshAbove mesh threshold W j =
        ⋃ side : Fin 2, ⋃ r ∈ s, point side r := by
    ext omega
    constructor
    · intro h
      rcases h with ⟨side, r, hr, hlt⟩
      exact Set.mem_iUnion.mpr
        ⟨side, Set.mem_iUnion₂.mpr ⟨r, hr, hlt⟩⟩
    · intro h
      rcases Set.mem_iUnion.mp h with ⟨side, hside⟩
      rcases Set.mem_iUnion₂.mp hside with ⟨r, hr, hlt⟩
      exact ⟨side, r, hr, hlt⟩
  calc
    mu (trackBTwoSidedMeshAbove mesh threshold W j)
        = mu (⋃ side : Fin 2, ⋃ r ∈ s, point side r) := by
          rw [hrewrite]
    _ ≤ ∑ side : Fin 2, mu (⋃ r ∈ s, point side r) := by
          rw [show (⋃ side : Fin 2, ⋃ r ∈ s, point side r) =
              ⋃ side ∈ (Finset.univ : Finset (Fin 2)),
                ⋃ r ∈ s, point side r by
            ext omega
            simp]
          simpa using
            MeasureTheory.measure_biUnion_finset_le
              (Finset.univ : Finset (Fin 2))
              (fun side => ⋃ r ∈ s, point side r)
    _ ≤ ∑ side : Fin 2, ∑ r ∈ s, mu (point side r) := by
          exact Finset.sum_le_sum fun side _hside =>
            MeasureTheory.measure_biUnion_finset_le s (point side)
    _ ≤
        ∑ side : Fin 2, ∑ r ∈ s,
          ENNReal.ofReal (upper side j r / threshold j) := by
          refine Finset.sum_le_sum fun side _hside => ?_
          refine Finset.sum_le_sum fun r hr => ?_
          exact measure_nonneg_gt_le_first
            (W := fun omega => W side j r omega)
            (A := threshold j)
            (V := upper side j r)
            (hthreshold j)
            (hint side j r hr)
            (hnonneg side j r hr)
            (hmean side j r hr)
    _ =
        trackBTwoSidedMeshFirstMomentBudget mesh threshold upper j := by
          rfl

/-- Partial sum of a mesh-indexed error family.  This is used for discarded
flat pieces and degree tails. -/
noncomputable def trackBMeshPartialSum
    (Z : ℕ → ℕ → Omega → ℝ) (j m : ℕ) (omega : Omega) : ℝ :=
  ∑ r ∈ Finset.Icc 1 m, Z j r omega

/-- Event that some partial sum of a mesh-indexed error family is larger than
the stage threshold in absolute value. -/
def trackBMeshPartialSumDeviation
    (mesh : ℕ → ℕ) (threshold : ℕ → ℝ)
    (Z : ℕ → ℕ → Omega → ℝ) (j : ℕ) : Set Omega :=
  {omega |
    ∃ m ∈ Finset.Icc 1 (mesh j),
      threshold j < |trackBMeshPartialSum Z j m omega|}

/-- Second-moment union-bound budget for `trackBMeshPartialSumDeviation`. -/
noncomputable def trackBMeshPartialSumSecondMomentBudget
    (mesh : ℕ → ℕ) (threshold : ℕ → ℝ)
    (partialSecond : ℕ → ℕ → ℝ) (j : ℕ) : ℝ≥0∞ :=
  ∑ m ∈ Finset.Icc 1 (mesh j),
    ENNReal.ofReal (partialSecond j m / (threshold j) ^ 2)

/-- Finite Markov plus union bound for maximum partial-sum deviations. -/
theorem measure_trackBMeshPartialSumDeviation_le_secondMomentBudget
    (mesh : ℕ → ℕ) (threshold : ℕ → ℝ)
    (Z : ℕ → ℕ → Omega → ℝ)
    (partialSecond : ℕ → ℕ → ℝ)
    (hthreshold : ∀ j, 0 < threshold j)
    (hint :
      ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
        Integrable
          (fun omega => (trackBMeshPartialSum Z j m omega) ^ 2) mu)
    (hsecond :
      ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
        (∫ omega, (trackBMeshPartialSum Z j m omega) ^ 2 ∂mu) ≤
          partialSecond j m)
    (j : ℕ) :
    mu (trackBMeshPartialSumDeviation mesh threshold Z j) ≤
      trackBMeshPartialSumSecondMomentBudget mesh threshold partialSecond j := by
  classical
  let s : Finset ℕ := Finset.Icc 1 (mesh j)
  let point : ℕ → Set Omega := fun m =>
    {omega | threshold j < |trackBMeshPartialSum Z j m omega|}
  have hsubset :
      trackBMeshPartialSumDeviation mesh threshold Z j ⊆
        ⋃ m ∈ s, point m := by
    intro omega hdev
    rcases hdev with ⟨m, hm, hbad⟩
    exact Set.mem_iUnion₂.mpr ⟨m, hm, hbad⟩
  calc
    mu (trackBMeshPartialSumDeviation mesh threshold Z j)
        ≤ mu (⋃ m ∈ s, point m) :=
          measure_mono hsubset
    _ ≤ ∑ m ∈ s, mu (point m) :=
          MeasureTheory.measure_biUnion_finset_le s point
    _ ≤
        ∑ m ∈ s,
          ENNReal.ofReal (partialSecond j m / (threshold j) ^ 2) := by
          exact Finset.sum_le_sum fun m hm =>
            measure_abs_error_gt_le_second
              (E := fun omega => trackBMeshPartialSum Z j m omega)
              (A := threshold j)
              (V := partialSecond j m)
              (hthreshold j)
              (hint j m hm)
              (hsecond j m hm)
    _ =
        trackBMeshPartialSumSecondMomentBudget mesh threshold
          partialSecond j := by
          rfl

/-- Total finite-core-to-complete budget, including the deterministic-grid
complete-to-squarefree second-moment budget. -/
noncomputable def trackBFiniteCoreToCompleteBudget
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) (A : ℕ → ℝ)
    (errorSecond : ℕ → ℕ → ℝ)
    (errProduct errBoundary errFlat errDegree errMOO errGaussian :
      ℕ → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  trackBFiniteCoreBlockBudget errProduct errBoundary errFlat errDegree
      errMOO errGaussian j +
    trackBGridSecondMomentBudget endpoint mesh A errorSecond j

theorem trackB_tsum_add_ne_top
    {a b : ℕ → ℝ≥0∞}
    (ha : (∑' j, a j) ≠ ⊤)
    (hb : (∑' j, b j) ≠ ⊤) :
    (∑' j, (a j + b j)) ≠ ⊤ := by
  rw [ENNReal.tsum_add]
  exact ENNReal.add_ne_top.mpr ⟨ha, hb⟩

/-- Componentwise finite error series imply summability of the full finite
Track B core-to-complete budget.  This is the Lean version of the polynomial
parameter-schedule check once each analytic error term has been bounded by a
summable sequence. -/
theorem trackBFiniteCoreToCompleteBudget_ne_top_of_components
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) (A : ℕ → ℝ)
    (errorSecond : ℕ → ℕ → ℝ)
    (errProduct errBoundary errFlat errDegree errMOO errGaussian :
      ℕ → ℝ≥0∞)
    (hProduct : (∑' j, errProduct j) ≠ ⊤)
    (hBoundary : (∑' j, errBoundary j) ≠ ⊤)
    (hFlat : (∑' j, errFlat j) ≠ ⊤)
    (hDegree : (∑' j, errDegree j) ≠ ⊤)
    (hMOO : (∑' j, errMOO j) ≠ ⊤)
    (hGaussian : (∑' j, errGaussian j) ≠ ⊤)
    (hGrid :
      (∑' j, trackBGridSecondMomentBudget endpoint mesh A errorSecond j) ≠ ⊤) :
    (∑' j,
      trackBFiniteCoreToCompleteBudget endpoint mesh A errorSecond
        errProduct errBoundary errFlat errDegree errMOO errGaussian j) ≠ ⊤ := by
  simpa [trackBFiniteCoreToCompleteBudget, trackBFiniteCoreBlockBudget,
    ENNReal.tsum_add, ENNReal.add_ne_top, add_assoc] using
    ⟨hProduct, hBoundary, hFlat, hDegree, hMOO, hGaussian, hGrid⟩

/-- Finite-core Track B certificate including the complete-to-squarefree
deterministic-grid error.

The only probability input about the squarefree process is
`prob_squarefree_block_fail`, whose right side is the sum of the six explicit
finite errors above.  The complete-model transfer then uses the existing
second-moment grid bound for `trackBError`.
-/
structure TrackBFiniteCoreToCompleteCertificate where
  params : TrackBFiniteCoreParameters
  endpoint : ℕ → ℕ → ℕ
  mesh : ℕ → ℕ
  level : ℕ → ℝ
  B : ℕ → ℝ
  A : ℕ → ℝ
  errorSecond : ℕ → ℕ → ℝ
  errProduct : ℕ → ℝ≥0∞
  errBoundary : ℕ → ℝ≥0∞
  errFlat : ℕ → ℝ≥0∞
  errDegree : ℕ → ℝ≥0∞
  errMOO : ℕ → ℝ≥0∞
  errGaussian : ℕ → ℝ≥0∞
  B_pos : ∀ j, 0 < B j
  A_pos : ∀ j, 0 < A j
  A_le_quarter_B : ∀ j, A j ≤ B j / 4
  level_le_half_B : ∀ j, level j ≤ B j / 2
  endpoint_tendsto_atTop :
    ∀ N0 : ℕ, ∀ᶠ j in atTop,
      ∀ m, m ∈ Finset.Icc 1 (mesh j) → N0 ≤ endpoint j m
  level_tendsto_atTop : Tendsto level atTop atTop
  B_tendsto_atTop : Tendsto B atTop atTop
  error_second_integrable :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      Integrable
        (fun omega => (trackBError omega (endpoint j m)) ^ 2) mu
  error_second_upper :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      (∫ omega, (trackBError omega (endpoint j m)) ^ 2 ∂mu) ≤
        errorSecond j m
  fail_summable :
    (∑' j,
      trackBFiniteCoreToCompleteBudget endpoint mesh A errorSecond
        errProduct errBoundary errFlat errDegree errMOO errGaussian j) ≠ ⊤
  prob_squarefree_block_fail :
    ∀ j,
      mu (trackBSquarefreeBlockFailure 0 endpoint mesh B j) ≤
        trackBFiniteCoreBlockBudget errProduct errBoundary errFlat errDegree
          errMOO errGaussian j

/-- Event-level version of the finite-core certificate.  This is the form one
gets directly from proving the six analytic estimates and the deterministic
implication that crossing failure forces at least one finite bad event. -/
structure TrackBFiniteCoreEventCertificate extends
    TrackBFiniteCoreToCompleteCertificate where
  bad : TrackBFiniteBadEvents
  squarefree_failure_subset_bad :
    ∀ j,
      trackBSquarefreeBlockFailure 0 endpoint mesh B j ⊆
        trackBFiniteCoreBadUnion bad j
  bad_prob :
    ∀ i j,
      mu (bad i j) ≤
        trackBFiniteErrorBudgetOf errProduct errBoundary errFlat errDegree
          errMOO errGaussian i j

/-- Event-level finite-core certificates discharge the older aggregate
squarefree-block probability field. -/
noncomputable def trackBFiniteCoreToCompleteCertificate_of_eventCertificate
    (h : TrackBFiniteCoreEventCertificate) :
    TrackBFiniteCoreToCompleteCertificate where
  params := h.params
  endpoint := h.endpoint
  mesh := h.mesh
  level := h.level
  B := h.B
  A := h.A
  errorSecond := h.errorSecond
  errProduct := h.errProduct
  errBoundary := h.errBoundary
  errFlat := h.errFlat
  errDegree := h.errDegree
  errMOO := h.errMOO
  errGaussian := h.errGaussian
  B_pos := h.B_pos
  A_pos := h.A_pos
  A_le_quarter_B := h.A_le_quarter_B
  level_le_half_B := h.level_le_half_B
  endpoint_tendsto_atTop := h.endpoint_tendsto_atTop
  level_tendsto_atTop := h.level_tendsto_atTop
  B_tendsto_atTop := h.B_tendsto_atTop
  error_second_integrable := h.error_second_integrable
  error_second_upper := h.error_second_upper
  fail_summable := h.fail_summable
  prob_squarefree_block_fail :=
    measure_trackBSquarefreeBlockFailure_le_finiteCoreBudget
      h.endpoint h.mesh h.B h.bad h.errProduct h.errBoundary h.errFlat
      h.errDegree h.errMOO h.errGaussian h.squarefree_failure_subset_bad
      h.bad_prob

/-- The finite-core certificate is exactly a fixed-base Track B
second-moment certificate, with the squarefree Brownian failure budget expanded
into the six finite analytic pieces. -/
noncomputable def trackBSecondMomentCertificate_of_finiteCoreToComplete
    (h : TrackBFiniteCoreToCompleteCertificate) :
    TrackBSecondMomentCertificate where
  base := 0
  endpoint := h.endpoint
  mesh := h.mesh
  level := h.level
  B := h.B
  A := h.A
  failBrownian := trackBFiniteCoreBlockBudget h.errProduct h.errBoundary
    h.errFlat h.errDegree h.errMOO h.errGaussian
  errorSecond := h.errorSecond
  B_pos := h.B_pos
  A_pos := h.A_pos
  A_le_quarter_B := h.A_le_quarter_B
  level_le_half_B := h.level_le_half_B
  endpoint_tendsto_atTop := h.endpoint_tendsto_atTop
  level_tendsto_atTop := h.level_tendsto_atTop
  B_tendsto_atTop := h.B_tendsto_atTop
  error_second_integrable := h.error_second_integrable
  error_second_upper := h.error_second_upper
  fail_summable := by
    simpa [trackBFiniteCoreToCompleteBudget] using h.fail_summable
  prob_brownian_fail := h.prob_squarefree_block_fail

/-- The refined finite-core Track B certificate proves the one-sided complete
model target through the already formalized fixed-base Track B transfer. -/
theorem erdos1144_of_trackBFiniteCoreToCompleteCertificate
    (h : TrackBFiniteCoreToCompleteCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBSquarefreeBrownianCertificate
    (trackBSquarefreeBrownianCertificate_of_secondMoment
      (trackBSecondMomentCertificate_of_finiteCoreToComplete h))

/-- Direct closure from the event-level finite-core certificate. -/
theorem erdos1144_of_trackBFiniteCoreEventCertificate
    (h : TrackBFiniteCoreEventCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBFiniteCoreToCompleteCertificate
    (trackBFiniteCoreToCompleteCertificate_of_eventCertificate h)

/-!
## Component-wise finite-core certificate

The next layer gives a more concrete source of the six bad-event estimates.
Product, rough-core Gaussian replacement, and Gaussian crossing failures are
supplied as direct probability inputs.
Boundary, flat, and degree failures are generated from finite first-moment and
second-moment estimates.
-/

/-- Direct probability input for one named finite bad event.  This is used for
the small-prime product event, the rough-core replacement event, and the
Gaussian crossing event. -/
structure TrackBDirectProbabilityInput (err : ℕ → ℝ≥0∞) where
  bad : ℕ → Set Omega
  prob : ∀ j, mu (bad j) ≤ err j

/-- A direct probability input can always be used with a larger error budget. -/
def TrackBDirectProbabilityInput.mono
    {err err' : ℕ → ℝ≥0∞}
    (h : TrackBDirectProbabilityInput err)
    (hle : ∀ j, err j ≤ err' j) :
    TrackBDirectProbabilityInput err' where
  bad := h.bad
  prob := fun j => (h.prob j).trans (hle j)

/-- Rough-core Gaussian replacement input.

The historical field name in the finite Track B certificate is still `moo`,
but the intended theorem is stronger than plain coordinate MOO invariance.  It
is a prefix-vector martingale CLT/lower-orthant replacement for the
degree-truncated rough squarefree core.  This wrapper gives that input a
correct Lean-facing name while remaining compatible with the existing event
slot. -/
structure TrackBRoughCoreGaussianReplacementCertificate
    (errRG : ℕ → ℝ≥0∞) where
  bad : ℕ → Set Omega
  prob : ∀ j, mu (bad j) ≤ errRG j

/-- Event-level wrapper for the prefix-vector martingale CLT replacement.

The finite coefficient predicates and lower-orthant approximation contract live
in `HarperTrackBPrefixMartingaleCLT`.  At the Track B block level we only need
the exceptional event and its probability budget; this wrapper records that the
legacy `moo` event slot is now fed by that prefix-martingale replacement. -/
structure TrackBPrefixMartingaleReplacementCertificate
    (errRG : ℕ → ℝ≥0∞) where
  bad : ℕ → Set Omega
  prob : ∀ j, mu (bad j) ≤ errRG j

/-- Prefix martingale replacement supplies the historical rough-core Gaussian
replacement event slot. -/
def TrackBPrefixMartingaleReplacementCertificate.toRoughCoreGaussianReplacement
    {errRG : ℕ → ℝ≥0∞}
    (h : TrackBPrefixMartingaleReplacementCertificate errRG) :
    TrackBRoughCoreGaussianReplacementCertificate errRG where
  bad := h.bad
  prob := h.prob

/-- Prefix martingale replacement supplies the direct probability input used by
the finite Track B event union. -/
def TrackBPrefixMartingaleReplacementCertificate.toDirectProbabilityInput
    {errRG : ℕ → ℝ≥0∞}
    (h : TrackBPrefixMartingaleReplacementCertificate errRG) :
    TrackBDirectProbabilityInput errRG where
  bad := h.bad
  prob := h.prob

/-- Rough-core Gaussian replacement supplies the direct probability input used
by the finite Track B event union. -/
def TrackBRoughCoreGaussianReplacementCertificate.toDirectProbabilityInput
    {errRG : ℕ → ℝ≥0∞}
    (h : TrackBRoughCoreGaussianReplacementCertificate errRG) :
    TrackBDirectProbabilityInput errRG where
  bad := h.bad
  prob := h.prob

/-- Three-term Gaussian crossing budget: reflection/small-height term,
discrete-mesh term, and variance-ratio or perturbation term. -/
noncomputable def trackBGaussianCrossingBudget
    (etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  etaTerm j + meshTerm j + varianceTerm j

/-- Componentwise summability for the three-term Gaussian crossing budget. -/
theorem trackBGaussianCrossingBudget_ne_top_of_components
    (etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞)
    (heta : (∑' j, etaTerm j) ≠ ⊤)
    (hmesh : (∑' j, meshTerm j) ≠ ⊤)
    (hvar : (∑' j, varianceTerm j) ≠ ⊤) :
    (∑' j, trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j) ≠
      ⊤ := by
  exact trackB_tsum_add_ne_top
    (trackB_tsum_add_ne_top heta hmesh) hvar

/-- Specialized Gaussian crossing input for the finite Track B block.

The intended analytic theorem is

```text
P(max_{m <= M_j} G_m < eta_j sqrt(M_j V_j))
  <= C_K Lambda_j^K (eta_j + M_j^{-1/2}) + perturb_j.
```

This structure records the event-level output in the same three-term shape,
while remaining directly compatible with the old `TrackBDirectProbabilityInput`
slot. -/
structure TrackBGaussianCrossingCertificate
    (etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞) where
  bad : ℕ → Set Omega
  prob :
    ∀ j, mu (bad j) ≤
      trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j

/-- Gaussian crossing certificates supply the direct probability input used by
the finite Track B event union. -/
def TrackBGaussianCrossingCertificate.toDirectProbabilityInput
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    (h : TrackBGaussianCrossingCertificate etaTerm meshTerm varianceTerm) :
    TrackBDirectProbabilityInput
      (trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm) where
  bad := h.bad
  prob := h.prob

/-- Gaussian crossing certificates also supply a direct probability input after
identifying an ambient error slot with the three-term crossing budget.  This is
used by the most concrete Track B certificate, whose inherited finite-core
fields still contain a single legacy `errGaussian` slot. -/
noncomputable def TrackBGaussianCrossingCertificate.toDirectProbabilityInputAs
    {etaTerm meshTerm varianceTerm errGaussian : ℕ → ℝ≥0∞}
    (h : TrackBGaussianCrossingCertificate etaTerm meshTerm varianceTerm)
    (herr :
      errGaussian = trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm) :
    TrackBDirectProbabilityInput errGaussian where
  bad := h.bad
  prob := by
    intro j
    rw [herr]
    exact h.prob j

/-- Gaussian crossing certificates supply a direct probability input for any
larger ambient Gaussian error budget. -/
noncomputable def TrackBGaussianCrossingCertificate.toDirectProbabilityInputLe
    {etaTerm meshTerm varianceTerm errGaussian : ℕ → ℝ≥0∞}
    (h : TrackBGaussianCrossingCertificate etaTerm meshTerm varianceTerm)
    (hle :
      ∀ j,
        trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j ≤
          errGaussian j) :
    TrackBDirectProbabilityInput errGaussian :=
  h.toDirectProbabilityInput.mono hle

/-!
### Small-prime product input

The product/diagonal event is analytically proved by combining:

* a lower tail for the full small-prime product;
* an upper tail for the full small-prime product;
* a Rankin tail comparing the full product to the truncated product.

The next definitions keep that decomposition visible while still producing the
single direct probability input consumed by the finite block theorem.
-/

/-- Product failure event generated by lower, upper, and truncation failures. -/
def trackBSmallPrimeProductBad
    (fullProduct truncatedProduct : ℕ → Omega → ℝ)
    (lower upper truncTolerance : ℕ → ℝ) (j : ℕ) : Set Omega :=
  {omega | (fullProduct j omega) ^ 2 < lower j} ∪
    {omega | upper j < (fullProduct j omega) ^ 2} ∪
      {omega | truncTolerance j <
        |fullProduct j omega - truncatedProduct j omega|}

/-- Three-piece budget for the product event. -/
noncomputable def trackBSmallPrimeProductBudget
    (errLower errUpper errTrunc : ℕ → ℝ≥0∞) (j : ℕ) : ℝ≥0∞ :=
  errLower j + errUpper j + errTrunc j

/-- Componentwise summability for the three small-prime product budgets. -/
theorem trackBSmallPrimeProductBudget_ne_top_of_components
    (errLower errUpper errTrunc : ℕ → ℝ≥0∞)
    (hLower : (∑' j, errLower j) ≠ ⊤)
    (hUpper : (∑' j, errUpper j) ≠ ⊤)
    (hTrunc : (∑' j, errTrunc j) ≠ ⊤) :
    (∑' j, trackBSmallPrimeProductBudget errLower errUpper errTrunc j) ≠
      ⊤ := by
  exact trackB_tsum_add_ne_top
    (trackB_tsum_add_ne_top hLower hUpper) hTrunc

/-- Union bound for the three product-event components. -/
theorem measure_trackBSmallPrimeProductBad_le
    (fullProduct truncatedProduct : ℕ → Omega → ℝ)
    (lower upper truncTolerance : ℕ → ℝ)
    (errLower errUpper errTrunc : ℕ → ℝ≥0∞)
    (hLower :
      ∀ j,
        mu {omega | (fullProduct j omega) ^ 2 < lower j} ≤ errLower j)
    (hUpper :
      ∀ j,
        mu {omega | upper j < (fullProduct j omega) ^ 2} ≤ errUpper j)
    (hTrunc :
      ∀ j,
        mu {omega | truncTolerance j <
          |fullProduct j omega - truncatedProduct j omega|} ≤ errTrunc j)
    (j : ℕ) :
    mu (trackBSmallPrimeProductBad fullProduct truncatedProduct lower upper
      truncTolerance j) ≤
      trackBSmallPrimeProductBudget errLower errUpper errTrunc j := by
  let A : Set Omega := {omega | (fullProduct j omega) ^ 2 < lower j}
  let B : Set Omega := {omega | upper j < (fullProduct j omega) ^ 2}
  let C : Set Omega :=
    {omega | truncTolerance j <
      |fullProduct j omega - truncatedProduct j omega|}
  calc
    mu (trackBSmallPrimeProductBad fullProduct truncatedProduct lower upper
        truncTolerance j)
        = mu (A ∪ B ∪ C) := by
          rfl
    _ = mu (A ∪ (B ∪ C)) := by
          rw [Set.union_assoc]
    _ ≤ mu A + mu (B ∪ C) :=
          measure_union_le A (B ∪ C)
    _ ≤ errLower j + (errUpper j + errTrunc j) := by
          exact add_le_add (hLower j)
            ((measure_union_le B C).trans
              (add_le_add (hUpper j) (hTrunc j)))
    _ =
        trackBSmallPrimeProductBudget errLower errUpper errTrunc j := by
          simp [trackBSmallPrimeProductBudget, add_assoc]

/-- Small-prime product certificate with the lower/upper/truncation pieces
named separately. -/
structure TrackBSmallPrimeProductCertificate (errProduct : ℕ → ℝ≥0∞) where
  fullProduct : ℕ → Omega → ℝ
  truncatedProduct : ℕ → Omega → ℝ
  lower : ℕ → ℝ
  upper : ℕ → ℝ
  truncTolerance : ℕ → ℝ
  errLower : ℕ → ℝ≥0∞
  errUpper : ℕ → ℝ≥0∞
  errTrunc : ℕ → ℝ≥0∞
  lower_prob :
    ∀ j,
      mu {omega | (fullProduct j omega) ^ 2 < lower j} ≤ errLower j
  upper_prob :
    ∀ j,
      mu {omega | upper j < (fullProduct j omega) ^ 2} ≤ errUpper j
  trunc_prob :
    ∀ j,
      mu {omega | truncTolerance j <
        |fullProduct j omega - truncatedProduct j omega|} ≤ errTrunc j
  budget_le :
    ∀ j,
      trackBSmallPrimeProductBudget errLower errUpper errTrunc j ≤
        errProduct j

/-- The small-prime product certificate supplies the direct product bad-event
probability input. -/
noncomputable def TrackBSmallPrimeProductCertificate.toDirectProbabilityInput
    {errProduct : ℕ → ℝ≥0∞}
    (h : TrackBSmallPrimeProductCertificate errProduct) :
    TrackBDirectProbabilityInput errProduct where
  bad := trackBSmallPrimeProductBad h.fullProduct h.truncatedProduct
    h.lower h.upper h.truncTolerance
  prob := by
    intro j
    exact
      (measure_trackBSmallPrimeProductBad_le h.fullProduct h.truncatedProduct
        h.lower h.upper h.truncTolerance h.errLower h.errUpper h.errTrunc
        h.lower_prob h.upper_prob h.trunc_prob j).trans
        (h.budget_le j)

/-- Small-prime product certificates can be used with a larger ambient budget. -/
noncomputable def TrackBSmallPrimeProductCertificate.mono
    {errProduct errProduct' : ℕ → ℝ≥0∞}
    (h : TrackBSmallPrimeProductCertificate errProduct)
    (hle : ∀ j, errProduct j ≤ errProduct' j) :
    TrackBSmallPrimeProductCertificate errProduct' where
  fullProduct := h.fullProduct
  truncatedProduct := h.truncatedProduct
  lower := h.lower
  upper := h.upper
  truncTolerance := h.truncTolerance
  errLower := h.errLower
  errUpper := h.errUpper
  errTrunc := h.errTrunc
  lower_prob := h.lower_prob
  upper_prob := h.upper_prob
  trunc_prob := h.trunc_prob
  budget_le := fun j => (h.budget_le j).trans (hle j)

/-- Boundary first-moment input.  It is intentionally generic: the analytic
boundary lemma only has to provide nonnegative energy variables, pointwise
first-moment bounds, and the deterministic budget comparison. -/
structure TrackBBoundaryMomentInput
    (mesh : ℕ → ℕ) (errBoundary : ℕ → ℝ≥0∞) where
  threshold : ℕ → ℝ
  energy : Fin 2 → ℕ → ℕ → Omega → ℝ
  upper : Fin 2 → ℕ → ℕ → ℝ
  threshold_pos : ∀ j, 0 < threshold j
  integrable :
    ∀ side j r, r ∈ Finset.Icc 1 (mesh j) →
      Integrable (fun omega => energy side j r omega) mu
  nonneg :
    ∀ side j r, r ∈ Finset.Icc 1 (mesh j) →
      0 ≤ᵐ[mu] fun omega => energy side j r omega
  mean :
    ∀ side j r, r ∈ Finset.Icc 1 (mesh j) →
      (∫ omega, energy side j r omega ∂mu) ≤ upper side j r
  budget_le :
    ∀ j,
      trackBTwoSidedMeshFirstMomentBudget mesh threshold upper j ≤
        errBoundary j

/-- Boundary first-moment inputs can be used with a larger ambient budget. -/
noncomputable def TrackBBoundaryMomentInput.mono
    {mesh : ℕ → ℕ} {errBoundary errBoundary' : ℕ → ℝ≥0∞}
    (h : TrackBBoundaryMomentInput mesh errBoundary)
    (hle : ∀ j, errBoundary j ≤ errBoundary' j) :
    TrackBBoundaryMomentInput mesh errBoundary' where
  threshold := h.threshold
  energy := h.energy
  upper := h.upper
  threshold_pos := h.threshold_pos
  integrable := h.integrable
  nonneg := h.nonneg
  mean := h.mean
  budget_le := fun j => (h.budget_le j).trans (hle j)

/-- Partial-sum second-moment input.  This is used for both the flat Rankin
tail and the degree-cutoff tail. -/
structure TrackBPartialSecondMomentInput
    (mesh : ℕ → ℕ) (err : ℕ → ℝ≥0∞) where
  threshold : ℕ → ℝ
  tail : ℕ → ℕ → Omega → ℝ
  partialSecond : ℕ → ℕ → ℝ
  threshold_pos : ∀ j, 0 < threshold j
  integrable :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      Integrable
        (fun omega => (trackBMeshPartialSum tail j m omega) ^ 2) mu
  second :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      (∫ omega, (trackBMeshPartialSum tail j m omega) ^ 2 ∂mu) ≤
        partialSecond j m
  budget_le :
    ∀ j,
      trackBMeshPartialSumSecondMomentBudget mesh threshold partialSecond j ≤
        err j

/-- Partial second-moment inputs can be used with a larger ambient budget. -/
noncomputable def TrackBPartialSecondMomentInput.mono
    {mesh : ℕ → ℕ} {err err' : ℕ → ℝ≥0∞}
    (h : TrackBPartialSecondMomentInput mesh err)
    (hle : ∀ j, err j ≤ err' j) :
    TrackBPartialSecondMomentInput mesh err' where
  threshold := h.threshold
  tail := h.tail
  partialSecond := h.partialSecond
  threshold_pos := h.threshold_pos
  integrable := h.integrable
  second := h.second
  budget_le := fun j => (h.budget_le j).trans (hle j)

/-- A squarefree-weighted representation certificate for a flat or degree
tail.  The analytic Rankin work only needs to bound the coefficient-square
sum; Lean then supplies the second-moment input using squarefree
orthogonality. -/
structure TrackBSquarefreeTailSecondMomentCertificate
    (mesh : ℕ → ℕ) (err : ℕ → ℝ≥0∞) where
  threshold : ℕ → ℝ
  tail : ℕ → ℕ → Omega → ℝ
  support : ℕ → ℕ → Finset ℕ
  weight : ℕ → ℕ → ℕ → ℝ
  partialSecond : ℕ → ℕ → ℝ
  threshold_pos : ∀ j, 0 < threshold j
  repr :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      ∀ omega,
        trackBMeshPartialSum tail j m omega =
          squarefreeWeightedSum (support j m) (weight j m) omega
  support_pos :
    ∀ j m n, m ∈ Finset.Icc 1 (mesh j) → n ∈ support j m → 0 < n
  support_squarefree :
    ∀ j m n, m ∈ Finset.Icc 1 (mesh j) → n ∈ support j m →
      Squarefree n
  coeff_second_le :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      (∑ n ∈ support j m, (weight j m n) ^ 2) ≤ partialSecond j m
  budget_le :
    ∀ j,
      trackBMeshPartialSumSecondMomentBudget mesh threshold partialSecond j ≤
        err j

/-- Squarefree tail certificates can be used with a larger ambient budget. -/
noncomputable def TrackBSquarefreeTailSecondMomentCertificate.mono
    {mesh : ℕ → ℕ} {err err' : ℕ → ℝ≥0∞}
    (h : TrackBSquarefreeTailSecondMomentCertificate mesh err)
    (hle : ∀ j, err j ≤ err' j) :
    TrackBSquarefreeTailSecondMomentCertificate mesh err' where
  threshold := h.threshold
  tail := h.tail
  support := h.support
  weight := h.weight
  partialSecond := h.partialSecond
  threshold_pos := h.threshold_pos
  repr := h.repr
  support_pos := h.support_pos
  support_squarefree := h.support_squarefree
  coeff_second_le := h.coeff_second_le
  budget_le := fun j => (h.budget_le j).trans (hle j)

/-- Squarefree tail representation certificates supply partial second-moment
inputs. -/
noncomputable def
    TrackBSquarefreeTailSecondMomentCertificate.toPartialSecondMomentInput
    {mesh : ℕ → ℕ} {err : ℕ → ℝ≥0∞}
    (h : TrackBSquarefreeTailSecondMomentCertificate mesh err) :
    TrackBPartialSecondMomentInput mesh err where
  threshold := h.threshold
  tail := h.tail
  partialSecond := h.partialSecond
  threshold_pos := h.threshold_pos
  integrable := by
    intro j m hm
    have hfun :
        (fun omega : Omega => (trackBMeshPartialSum h.tail j m omega) ^ 2)
          =
        (fun omega : Omega =>
          (squarefreeWeightedSum (h.support j m) (h.weight j m) omega) ^ 2) := by
      funext omega
      rw [h.repr j m hm omega]
    rw [hfun]
    exact integrable_squarefreeWeightedSum_sq (h.support j m) (h.weight j m)
  second := by
    intro j m hm
    have hfun :
        (fun omega : Omega => (trackBMeshPartialSum h.tail j m omega) ^ 2)
          =
        (fun omega : Omega =>
          (squarefreeWeightedSum (h.support j m) (h.weight j m) omega) ^ 2) := by
      funext omega
      rw [h.repr j m hm omega]
    rw [hfun]
    calc
      ∫ omega,
          (squarefreeWeightedSum (h.support j m) (h.weight j m) omega) ^ 2 ∂mu
          =
          ∑ n ∈ h.support j m, (h.weight j m n) ^ 2 := by
            exact
              integral_squarefreeWeightedSum_sq_eq_diag
                (h.support j m) (h.weight j m)
                (fun n hn => h.support_pos j m n hm hn)
                (fun n hn => h.support_squarefree j m n hm hn)
      _ ≤ h.partialSecond j m := h.coeff_second_le j m hm
  budget_le := h.budget_le

/-!
### Complete-to-squarefree grid error from squarefree coefficients

The Track B transfer still needs second moments for
`trackBError omega (endpoint j m)`.  The intended elementary proof represents
this error as a squarefree weighted sum with very small deterministic
coefficients.  The next certificate discharges the integrability and
second-moment fields from such a representation.
-/

/-- Squarefree weighted representation for the complete-to-squarefree grid
error on the deterministic Track B grid. -/
structure TrackBGridErrorSquarefreeMomentInput
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ)
    (errorSecond : ℕ → ℕ → ℝ) where
  support : ℕ → ℕ → Finset ℕ
  weight : ℕ → ℕ → ℕ → ℝ
  repr :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      ∀ omega,
        trackBError omega (endpoint j m) =
          squarefreeWeightedSum (support j m) (weight j m) omega
  support_pos :
    ∀ j m n, m ∈ Finset.Icc 1 (mesh j) → n ∈ support j m → 0 < n
  support_squarefree :
    ∀ j m n, m ∈ Finset.Icc 1 (mesh j) → n ∈ support j m →
      Squarefree n
  coeff_second_le :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      (∑ n ∈ support j m, (weight j m n) ^ 2) ≤ errorSecond j m

/-- Grid-error squarefree representations provide the integrability field used
by the Track B transfer. -/
theorem TrackBGridErrorSquarefreeMomentInput.integrable
    {endpoint : ℕ → ℕ → ℕ} {mesh : ℕ → ℕ}
    {errorSecond : ℕ → ℕ → ℝ}
    (h : TrackBGridErrorSquarefreeMomentInput endpoint mesh errorSecond) :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      Integrable
        (fun omega => (trackBError omega (endpoint j m)) ^ 2) mu := by
  intro j m hm
  have hfun :
      (fun omega : Omega => (trackBError omega (endpoint j m)) ^ 2)
        =
      (fun omega : Omega =>
        (squarefreeWeightedSum (h.support j m) (h.weight j m) omega) ^ 2) := by
    funext omega
    rw [h.repr j m hm omega]
  rw [hfun]
  exact integrable_squarefreeWeightedSum_sq (h.support j m) (h.weight j m)

/-- Grid-error squarefree representations provide the second-moment upper
field used by the Track B transfer. -/
theorem TrackBGridErrorSquarefreeMomentInput.second_upper
    {endpoint : ℕ → ℕ → ℕ} {mesh : ℕ → ℕ}
    {errorSecond : ℕ → ℕ → ℝ}
    (h : TrackBGridErrorSquarefreeMomentInput endpoint mesh errorSecond) :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      (∫ omega, (trackBError omega (endpoint j m)) ^ 2 ∂mu) ≤
        errorSecond j m := by
  intro j m hm
  have hfun :
      (fun omega : Omega => (trackBError omega (endpoint j m)) ^ 2)
        =
      (fun omega : Omega =>
        (squarefreeWeightedSum (h.support j m) (h.weight j m) omega) ^ 2) := by
    funext omega
    rw [h.repr j m hm omega]
  rw [hfun]
  calc
    ∫ omega,
        (squarefreeWeightedSum (h.support j m) (h.weight j m) omega) ^ 2 ∂mu
        =
        ∑ n ∈ h.support j m, (h.weight j m n) ^ 2 := by
          exact
            integral_squarefreeWeightedSum_sq_eq_diag
              (h.support j m) (h.weight j m)
              (fun n hn => h.support_pos j m n hm hn)
              (fun n hn => h.support_squarefree j m n hm hn)
    _ ≤ errorSecond j m := h.coeff_second_le j m hm

/-- A pointwise coefficient version of the complete-to-squarefree grid-error
input.

For the exact complete-to-squarefree transfer one expects `support j m` to be
the squarefree integers up to `endpoint j m + 1` and the deterministic
coefficient bound

```text
|weight d| <= 1 / sqrt(endpoint j m + 1).
```

Together with `support.card <= endpoint j m + 1`, this implies the uniform
second-moment bound `E error^2 <= 1`.  This structure keeps the remaining
floor/square-root arithmetic separate from the probability calculation. -/
structure TrackBGridErrorPointwiseMomentInput
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) where
  support : ℕ → ℕ → Finset ℕ
  weight : ℕ → ℕ → ℕ → ℝ
  repr :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      ∀ omega,
        trackBError omega (endpoint j m) =
          squarefreeWeightedSum (support j m) (weight j m) omega
  support_pos :
    ∀ j m n, m ∈ Finset.Icc 1 (mesh j) → n ∈ support j m → 0 < n
  support_squarefree :
    ∀ j m n, m ∈ Finset.Icc 1 (mesh j) → n ∈ support j m →
      Squarefree n
  support_card_le :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      ((support j m).card : ℝ) ≤ ((endpoint j m + 1 : ℕ) : ℝ)
  coeff_abs_le :
    ∀ j m n, m ∈ Finset.Icc 1 (mesh j) → n ∈ support j m →
      |weight j m n| ≤ (Real.sqrt (((endpoint j m + 1 : ℕ) : ℝ)))⁻¹

/-- Pointwise coefficient control gives the coefficient-square budget `1`. -/
theorem TrackBGridErrorPointwiseMomentInput.coeff_second_le_one
    {endpoint : ℕ → ℕ → ℕ} {mesh : ℕ → ℕ}
    (h : TrackBGridErrorPointwiseMomentInput endpoint mesh) :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      (∑ n ∈ h.support j m, (h.weight j m n) ^ 2) ≤ 1 := by
  intro j m hm
  let N : ℕ := endpoint j m + 1
  have hN_pos_nat : 0 < N := by
    dsimp [N]
    exact Nat.succ_pos _
  have hN_pos_real : 0 < ((N : ℕ) : ℝ) := by exact_mod_cast hN_pos_nat
  have hsqrt_pos : 0 < Real.sqrt (((N : ℕ) : ℝ)) :=
    Real.sqrt_pos_of_pos hN_pos_real
  have hterm :
      ∀ n ∈ h.support j m,
        (h.weight j m n) ^ 2 ≤
          (Real.sqrt (((N : ℕ) : ℝ)))⁻¹ ^ 2 := by
    intro n hn
    have habs :
        |h.weight j m n| ≤
          (Real.sqrt (((N : ℕ) : ℝ)))⁻¹ := by
      simpa [N] using h.coeff_abs_le j m n hm hn
    have hinv_nonneg :
        0 ≤ (Real.sqrt (((N : ℕ) : ℝ)))⁻¹ :=
      inv_nonneg.mpr (Real.sqrt_nonneg _)
    exact sq_le_sq.mpr (by simpa [abs_of_nonneg hinv_nonneg] using habs)
  calc
    (∑ n ∈ h.support j m, (h.weight j m n) ^ 2)
        ≤
      ∑ n ∈ h.support j m,
        (Real.sqrt (((N : ℕ) : ℝ)))⁻¹ ^ 2 := by
        exact Finset.sum_le_sum fun n hn => hterm n hn
    _ =
      ((h.support j m).card : ℝ) *
        (Real.sqrt (((N : ℕ) : ℝ)))⁻¹ ^ 2 := by
        simp
    _ ≤
      ((N : ℕ) : ℝ) *
        (Real.sqrt (((N : ℕ) : ℝ)))⁻¹ ^ 2 := by
        have hcard :
            ((h.support j m).card : ℝ) ≤ ((N : ℕ) : ℝ) := by
          simpa [N] using h.support_card_le j m hm
        exact mul_le_mul_of_nonneg_right hcard (sq_nonneg _)
    _ = 1 := by
        rw [show (Real.sqrt (((N : ℕ) : ℝ)))⁻¹ ^ 2 =
            ((Real.sqrt (((N : ℕ) : ℝ)) ^ 2)⁻¹) by
            rw [inv_pow]]
        rw [Real.sq_sqrt (le_of_lt hN_pos_real)]
        field_simp [hN_pos_real.ne']

/-- Pointwise grid-error coefficient control supplies the squarefree moment
input with the uniform budget `1`. -/
def TrackBGridErrorPointwiseMomentInput.toSquarefreeMomentInput
    {endpoint : ℕ → ℕ → ℕ} {mesh : ℕ → ℕ}
    (h : TrackBGridErrorPointwiseMomentInput endpoint mesh) :
    TrackBGridErrorSquarefreeMomentInput endpoint mesh (fun _ _ => 1) where
  support := h.support
  weight := h.weight
  repr := h.repr
  support_pos := h.support_pos
  support_squarefree := h.support_squarefree
  coeff_second_le := h.coeff_second_le_one

/-- Canonical squarefree support for the Track B complete-to-squarefree error
at shifted endpoint `N`. -/
noncomputable def trackBGridErrorCanonicalSupport (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (N + 1)).filter Squarefree

/-- Canonical coefficient in the identity

```text
S(N+1)/sqrt(N+1) - sum_{d<=N+1, sf} f(d)/sqrt(d)
  = sum_{d<=N+1, sf} f(d) *
      ( floor_sqrt((N+1)/d)/sqrt(N+1) - 1/sqrt(d) ).
```

The representation and the pointwise bound for this coefficient are the two
remaining elementary arithmetic obligations for the complete-to-squarefree
grid-error estimate. -/
noncomputable def trackBGridErrorCanonicalWeight (N d : ℕ) : ℝ :=
  ((Nat.sqrt ((N + 1) / d) : ℕ) : ℝ) /
      Real.sqrt (((N + 1 : ℕ) : ℝ)) -
    (Real.sqrt ((d : ℕ) : ℝ))⁻¹

/-- Complete-side canonical squarefree coefficient before subtracting the
critical squarefree approximation. -/
noncomputable def trackBCompleteCanonicalWeight (N d : ℕ) : ℝ :=
  ((Nat.sqrt ((N + 1) / d) : ℕ) : ℝ) /
    Real.sqrt (((N + 1 : ℕ) : ℝ))

/-- Unnormalized complete-side squarefree coefficient for cutoff `n`.

The exact square-kernel arithmetic theorem for Track B should prove

```text
S(n) = sum_{d <= n, d squarefree} f(d) * floor_sqrt(n / d).
```

This coefficient is the finite-sum form of that theorem before dividing by
`sqrt n`.
-/
noncomputable def trackBCompleteCanonicalUnnormalizedWeight
    (n d : ℕ) : ℝ :=
  ((Nat.sqrt (n / d) : ℕ) : ℝ)

/-- The normalized complete coefficient is the unnormalized coefficient divided
by `sqrt(N+1)`. -/
theorem trackBCompleteCanonicalWeight_eq_unnormalized
    (N d : ℕ) :
    trackBCompleteCanonicalWeight N d =
      trackBCompleteCanonicalUnnormalizedWeight (N + 1) d /
        Real.sqrt (((N + 1 : ℕ) : ℝ)) := by
  rfl

/-- The unnormalized canonical complete-side squarefree sum can be written as
a counted square-multiplier sum.

This proves the "coefficient side" of the square-kernel reindexing:
`Nat.sqrt (n / d)` is exactly the number of positive square multipliers `k`
with `k^2 d <= n`.  The remaining arithmetic step is the Fubini identity
turning the summatory square-smoothing formula into this counted sum.
-/
theorem canonicalUnnormalizedWeightedSum_eq_squareMultiplierCount
    (omega : Omega) (n : ℕ) :
    squarefreeWeightedSum ((Finset.Icc 1 n).filter Squarefree)
        (trackBCompleteCanonicalUnnormalizedWeight n) omega =
      ∑ d ∈ Finset.Icc 1 n,
        ∑ _k ∈ (Finset.Icc 1 n).filter (fun k => k ^ 2 * d ≤ n),
          gSquarefree omega d := by
  classical
  unfold squarefreeWeightedSum trackBCompleteCanonicalUnnormalizedWeight
  calc
    (∑ d ∈ (Finset.Icc 1 n).filter Squarefree,
        ((Nat.sqrt (n / d) : ℕ) : ℝ) * gSquarefree omega d)
        =
      ∑ d ∈ Finset.Icc 1 n,
        ((Nat.sqrt (n / d) : ℕ) : ℝ) * gSquarefree omega d := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl ?_
        intro d hd
        by_cases hsf : Squarefree d
        · simp [hsf]
        · simp [hsf, gSquarefree]
    _ =
      ∑ d ∈ Finset.Icc 1 n,
        (( ((Finset.Icc 1 n).filter fun k => k ^ 2 * d ≤ n).card : ℕ) : ℝ) *
          gSquarefree omega d := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        have hdpos : 0 < d := (Finset.mem_Icc.mp hd).1
        rw [card_square_multipliers_le n d hdpos]
    _ =
      ∑ d ∈ Finset.Icc 1 n,
        ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k ^ 2 * d ≤ n),
          gSquarefree omega d := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        simp [mul_comm]

/-- The proved summatory square-smoothing identity, together with the finite
Fubini/counting lemmas, gives the unnormalized canonical complete expansion.

The remaining complete-to-squarefree arithmetic input is now only the
pointwise square-kernel identity `f_eq_squareSmoothing`; the summatory
reindexing and canonical coefficient count are proved.
-/
theorem S_eq_canonicalUnnormalized_of_squareSmoothing
    (omega : Omega) (n : ℕ) :
    S omega n =
      squarefreeWeightedSum ((Finset.Icc 1 n).filter Squarefree)
        (trackBCompleteCanonicalUnnormalizedWeight n) omega := by
  rw [S_eq_squareSmoothing omega n]
  rw [sum_GSquarefree_div_sq_eq_squareMultiplierCount omega n]
  exact (canonicalUnnormalizedWeightedSum_eq_squareMultiplierCount omega n).symm

/-- An unnormalized canonical expansion of `S(N+1)` immediately gives the
normalized canonical expansion of `normSum N`.

This isolates the remaining square-kernel arithmetic as an unnormalized
finite-sum reindexing theorem.  Once that theorem is proved, all Track B
grid-error moment estimates follow from the already-proved coefficient bound.
-/
theorem normSum_eq_canonicalWeightedSum_of_S_eq_unnormalized
    (omega : Omega) (N : ℕ)
    (hS :
      S omega (N + 1) =
        squarefreeWeightedSum (trackBGridErrorCanonicalSupport N)
          (trackBCompleteCanonicalUnnormalizedWeight (N + 1)) omega) :
    normSum omega N =
      squarefreeWeightedSum (trackBGridErrorCanonicalSupport N)
        (trackBCompleteCanonicalWeight N) omega := by
  classical
  unfold normSum
  rw [hS]
  unfold squarefreeWeightedSum trackBCompleteCanonicalWeight
    trackBCompleteCanonicalUnnormalizedWeight
  rw [Finset.sum_div]
  refine Finset.sum_congr rfl ?_
  intro d _hd
  ring

theorem trackBGridErrorCanonicalWeight_le_zero_aux
    {n d : ℕ} (hnpos : 0 < n) (hdpos : 0 < d) :
    ((Nat.sqrt (n / d) : ℝ) / Real.sqrt ((n : ℕ) : ℝ) -
        (Real.sqrt ((d : ℕ) : ℝ))⁻¹) ≤ 0 := by
  let k := Nat.sqrt (n / d)
  have hnR : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast hnpos
  have hdR : 0 < ((d : ℕ) : ℝ) := by exact_mod_cast hdpos
  have hsn : 0 < Real.sqrt ((n : ℕ) : ℝ) := Real.sqrt_pos_of_pos hnR
  have hsd : 0 < Real.sqrt ((d : ℕ) : ℝ) := Real.sqrt_pos_of_pos hdR
  have hnat : d * k ^ 2 ≤ n := by
    dsimp [k]
    calc
      d * (Nat.sqrt (n / d)) ^ 2 ≤ d * (n / d) := by
        exact Nat.mul_le_mul_left d (Nat.sqrt_le' (n / d))
      _ = (n / d) * d := by ring
      _ ≤ n := Nat.div_mul_le_self n d
  have hsq :
      ((k : ℝ) * Real.sqrt ((d : ℕ) : ℝ)) ^ 2 ≤
        (Real.sqrt ((n : ℕ) : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hdR),
      Real.sq_sqrt (le_of_lt hnR)]
    have hnat_comm : k ^ 2 * d ≤ n := by
      simpa [Nat.mul_comm] using hnat
    exact_mod_cast hnat_comm
  have hmul :
      (k : ℝ) * Real.sqrt ((d : ℕ) : ℝ) ≤
        Real.sqrt ((n : ℕ) : ℝ) := by
    have habs := sq_le_sq.mp hsq
    simpa [abs_of_nonneg
        (mul_nonneg (by positivity) (Real.sqrt_nonneg _)),
      abs_of_nonneg (Real.sqrt_nonneg _)] using habs
  have hdiv1 :
      (k : ℝ) ≤ Real.sqrt ((n : ℕ) : ℝ) /
        Real.sqrt ((d : ℕ) : ℝ) := by
    rw [le_div_iff₀ hsd]
    simpa [mul_comm] using hmul
  have hdiv :
      (k : ℝ) / Real.sqrt ((n : ℕ) : ℝ) ≤
        (Real.sqrt ((d : ℕ) : ℝ))⁻¹ := by
    calc
      (k : ℝ) / Real.sqrt ((n : ℕ) : ℝ) ≤
          (Real.sqrt ((n : ℕ) : ℝ) / Real.sqrt ((d : ℕ) : ℝ)) /
            Real.sqrt ((n : ℕ) : ℝ) := by
        exact div_le_div_of_nonneg_right hdiv1 (le_of_lt hsn)
      _ = (Real.sqrt ((d : ℕ) : ℝ))⁻¹ := by
        field_simp [hsn.ne', hsd.ne']
  linarith

theorem trackBGridErrorCanonicalWeight_ge_neg_aux
    {n d : ℕ} (hnpos : 0 < n) (hdpos : 0 < d) :
    - (Real.sqrt ((n : ℕ) : ℝ))⁻¹ ≤
      ((Nat.sqrt (n / d) : ℝ) / Real.sqrt ((n : ℕ) : ℝ) -
        (Real.sqrt ((d : ℕ) : ℝ))⁻¹) := by
  let k := Nat.sqrt (n / d)
  have hnR : 0 < ((n : ℕ) : ℝ) := by exact_mod_cast hnpos
  have hdR : 0 < ((d : ℕ) : ℝ) := by exact_mod_cast hdpos
  have hsn : 0 < Real.sqrt ((n : ℕ) : ℝ) := Real.sqrt_pos_of_pos hnR
  have hsd : 0 < Real.sqrt ((d : ℕ) : ℝ) := Real.sqrt_pos_of_pos hdR
  have hnat : n ≤ d * (k + 1) ^ 2 := by
    dsimp [k]
    have hmod : n % d < d := Nat.mod_lt n hdpos
    have hlt : n < d * (n / d + 1) := by
      calc
        n = n % d + d * (n / d) := by rw [Nat.mod_add_div]
        _ < d + d * (n / d) := Nat.add_lt_add_right hmod _
        _ = d * (n / d + 1) := by ring
    have hq :
        n / d + 1 ≤ (Nat.sqrt (n / d) + 1) ^ 2 :=
      Nat.succ_le_succ_sqrt' (n / d)
    have hle :
        d * (n / d + 1) ≤
          d * (Nat.sqrt (n / d) + 1) ^ 2 := by
      exact Nat.mul_le_mul_left d hq
    exact le_trans (le_of_lt hlt) hle
  have hsq :
      (Real.sqrt ((n : ℕ) : ℝ)) ^ 2 ≤
        (((k + 1 : ℕ) : ℝ) * Real.sqrt ((d : ℕ) : ℝ)) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (le_of_lt hnR),
      Real.sq_sqrt (le_of_lt hdR)]
    norm_num
    have hnat_comm : n ≤ (k + 1) ^ 2 * d := by
      simpa [Nat.mul_comm] using hnat
    exact_mod_cast hnat_comm
  have hmul :
      Real.sqrt ((n : ℕ) : ℝ) ≤
        ((k + 1 : ℕ) : ℝ) * Real.sqrt ((d : ℕ) : ℝ) := by
    have habs := sq_le_sq.mp hsq
    have hk1_nonneg : 0 ≤ ((k : ℝ) + 1) := by positivity
    have hcast : (((k + 1 : ℕ) : ℝ)) = (k : ℝ) + 1 := by
      norm_num
    rw [hcast]
    rw [hcast] at habs
    simpa [abs_of_nonneg (Real.sqrt_nonneg _),
      abs_of_nonneg (mul_nonneg hk1_nonneg (Real.sqrt_nonneg _)),
      abs_of_nonneg hk1_nonneg] using habs
  have hdiv :
      (Real.sqrt ((d : ℕ) : ℝ))⁻¹ ≤
        (((k + 1 : ℕ) : ℝ)) / Real.sqrt ((n : ℕ) : ℝ) := by
    rw [le_div_iff₀ hsn]
    rw [inv_mul_eq_div]
    rw [div_le_iff₀ hsd]
    simpa [mul_comm] using hmul
  have hone :
      (((k + 1 : ℕ) : ℝ) / Real.sqrt ((n : ℕ) : ℝ)) =
        (k : ℝ) / Real.sqrt ((n : ℕ) : ℝ) +
          (Real.sqrt ((n : ℕ) : ℝ))⁻¹ := by
    norm_num [Nat.cast_add, add_div, one_div]
  rw [hone] at hdiv
  linarith

/-- The canonical complete-to-squarefree coefficient is uniformly bounded by
`1 / sqrt(N+1)`. -/
theorem trackBGridErrorCanonicalWeight_abs_le
    {N d : ℕ} (hdpos : 0 < d) :
    |trackBGridErrorCanonicalWeight N d| ≤
      (Real.sqrt (((N + 1 : ℕ) : ℝ)))⁻¹ := by
  unfold trackBGridErrorCanonicalWeight
  let n : ℕ := N + 1
  have hnpos : 0 < n := by
    dsimp [n]
    exact Nat.succ_pos _
  have hle0 :=
    trackBGridErrorCanonicalWeight_le_zero_aux
      (n := n) (d := d) hnpos hdpos
  have hge :=
    trackBGridErrorCanonicalWeight_ge_neg_aux
      (n := n) (d := d) hnpos hdpos
  dsimp [n] at hle0 hge
  rw [abs_of_nonpos hle0]
  linarith

theorem trackBGridErrorCanonicalSupport_pos
    {N d : ℕ} (hd : d ∈ trackBGridErrorCanonicalSupport N) :
    0 < d := by
  rw [trackBGridErrorCanonicalSupport, Finset.mem_filter, Finset.mem_Icc] at hd
  exact hd.1.1

theorem trackBGridErrorCanonicalSupport_squarefree
    {N d : ℕ} (hd : d ∈ trackBGridErrorCanonicalSupport N) :
    Squarefree d := by
  rw [trackBGridErrorCanonicalSupport, Finset.mem_filter] at hd
  exact hd.2

theorem trackBGridErrorCanonicalSupport_card_le (N : ℕ) :
    ((trackBGridErrorCanonicalSupport N).card : ℝ) ≤
      (((N + 1 : ℕ) : ℝ)) := by
  have hcard_nat :
      (trackBGridErrorCanonicalSupport N).card ≤ N + 1 := by
    calc
      (trackBGridErrorCanonicalSupport N).card
          ≤ (Finset.Icc 1 (N + 1)).card := by
          exact Finset.card_filter_le _ _
      _ = N + 1 := by
          simp
  exact_mod_cast hcard_nat

/-- The squarefree critical sum is the canonical squarefree weighted sum with
coefficient `1 / sqrt(d)`. -/
theorem squarefreeCriticalSum_eq_canonicalWeightedSum (omega : Omega) (N : ℕ) :
    squarefreeCriticalSum omega N =
      squarefreeWeightedSum (trackBGridErrorCanonicalSupport N)
        (fun d => (Real.sqrt ((d : ℕ) : ℝ))⁻¹) omega := by
  classical
  unfold squarefreeCriticalSum squarefreeWeightedSum
    trackBGridErrorCanonicalSupport
  rw [Finset.sum_filter]
  refine Finset.sum_congr rfl ?_
  intro d hd
  by_cases hsf : Squarefree d
  · simp [hsf, div_eq_mul_inv, mul_comm]
  · simp [hsf]

/-- If the complete normalized sum has the canonical squarefree expansion,
then the Track B error has the canonical coefficient representation. -/
theorem trackBError_eq_canonicalWeightedSum_of_normSum_eq
    (omega : Omega) (N : ℕ)
    (hcomplete :
      normSum omega N =
        squarefreeWeightedSum (trackBGridErrorCanonicalSupport N)
          (trackBCompleteCanonicalWeight N) omega) :
    trackBError omega N =
      squarefreeWeightedSum (trackBGridErrorCanonicalSupport N)
        (trackBGridErrorCanonicalWeight N) omega := by
  classical
  rw [trackBError, hcomplete,
    squarefreeCriticalSum_eq_canonicalWeightedSum omega N]
  unfold squarefreeWeightedSum trackBGridErrorCanonicalWeight
    trackBCompleteCanonicalWeight
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro d hd
  ring

/-- Canonical coefficient input for the grid-error moment.  Compared with
`TrackBGridErrorPointwiseMomentInput`, the support and coefficient are fixed;
future work only has to prove the representation and the deterministic
coefficient bound. -/
structure TrackBGridErrorCanonicalMomentInput
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) where
  repr :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      ∀ omega,
        trackBError omega (endpoint j m) =
          squarefreeWeightedSum
            (trackBGridErrorCanonicalSupport (endpoint j m))
            (trackBGridErrorCanonicalWeight (endpoint j m)) omega
  coeff_abs_le :
    ∀ j m d, m ∈ Finset.Icc 1 (mesh j) →
      d ∈ trackBGridErrorCanonicalSupport (endpoint j m) →
        |trackBGridErrorCanonicalWeight (endpoint j m) d| ≤
          (Real.sqrt (((endpoint j m + 1 : ℕ) : ℝ)))⁻¹

/-- The canonical grid-error input is enough for the uniform grid-error
second-moment budget. -/
noncomputable def TrackBGridErrorCanonicalMomentInput.toPointwiseMomentInput
    {endpoint : ℕ → ℕ → ℕ} {mesh : ℕ → ℕ}
    (h : TrackBGridErrorCanonicalMomentInput endpoint mesh) :
    TrackBGridErrorPointwiseMomentInput endpoint mesh where
  support j m := trackBGridErrorCanonicalSupport (endpoint j m)
  weight j m := trackBGridErrorCanonicalWeight (endpoint j m)
  repr := h.repr
  support_pos := by
    intro j m n _hm hn
    exact trackBGridErrorCanonicalSupport_pos hn
  support_squarefree := by
    intro j m n _hm hn
    exact trackBGridErrorCanonicalSupport_squarefree hn
  support_card_le := by
    intro j m _hm
    exact trackBGridErrorCanonicalSupport_card_le (endpoint j m)
  coeff_abs_le := h.coeff_abs_le

/-- Canonical grid-error arithmetic supplies the squarefree moment input with
budget `1`. -/
noncomputable def TrackBGridErrorCanonicalMomentInput.toSquarefreeMomentInput
    {endpoint : ℕ → ℕ → ℕ} {mesh : ℕ → ℕ}
    (h : TrackBGridErrorCanonicalMomentInput endpoint mesh) :
    TrackBGridErrorSquarefreeMomentInput endpoint mesh (fun _ _ => 1) :=
  h.toPointwiseMomentInput.toSquarefreeMomentInput

/-- Canonical grid-error input where only the exact representation remains to
be supplied; the coefficient bound is already proved above. -/
structure TrackBGridErrorCanonicalRepresentationInput
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) where
  repr :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      ∀ omega,
        trackBError omega (endpoint j m) =
          squarefreeWeightedSum
            (trackBGridErrorCanonicalSupport (endpoint j m))
            (trackBGridErrorCanonicalWeight (endpoint j m)) omega

/-- Canonical expansion input for the normalized complete sum.  This is the
remaining square-kernel arithmetic theorem in its cleanest Track B form. -/
structure TrackBCompleteCanonicalExpansionInput
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) where
  norm_repr :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      ∀ omega,
        normSum omega (endpoint j m) =
          squarefreeWeightedSum
            (trackBGridErrorCanonicalSupport (endpoint j m))
            (trackBCompleteCanonicalWeight (endpoint j m)) omega

/-- Unnormalized canonical expansion input for the complete sum.  This is the
most convenient target for the finite square-kernel reindexing proof. -/
structure TrackBCompleteCanonicalUnnormalizedExpansionInput
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) where
  sum_repr :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      ∀ omega,
        S omega (endpoint j m + 1) =
          squarefreeWeightedSum
            (trackBGridErrorCanonicalSupport (endpoint j m))
            (trackBCompleteCanonicalUnnormalizedWeight (endpoint j m + 1))
            omega

/-- The unnormalized canonical expansion supplies the normalized complete
canonical expansion. -/
noncomputable def
    TrackBCompleteCanonicalUnnormalizedExpansionInput.toExpansionInput
    {endpoint : ℕ → ℕ → ℕ} {mesh : ℕ → ℕ}
    (h : TrackBCompleteCanonicalUnnormalizedExpansionInput endpoint mesh) :
    TrackBCompleteCanonicalExpansionInput endpoint mesh where
  norm_repr := by
    intro j m hm omega
    exact
      normSum_eq_canonicalWeightedSum_of_S_eq_unnormalized omega
        (endpoint j m) (h.sum_repr j m hm omega)

/-- A global unnormalized canonical expansion specializes to every Track B
grid. -/
structure TrackBCompleteCanonicalUnnormalizedExpansionAll where
  sum_repr_all :
    ∀ omega N,
      S omega N =
        squarefreeWeightedSum ((Finset.Icc 1 N).filter Squarefree)
          (trackBCompleteCanonicalUnnormalizedWeight N) omega

/-- The summatory square-smoothing identity supplies the global unnormalized
canonical expansion input. -/
noncomputable def trackBCompleteCanonicalUnnormalizedExpansionAll_of_squareSmoothing :
    TrackBCompleteCanonicalUnnormalizedExpansionAll where
  sum_repr_all := S_eq_canonicalUnnormalized_of_squareSmoothing

/-- Global unnormalized canonical expansion supplies the grid-level expansion
input. -/
noncomputable def TrackBCompleteCanonicalUnnormalizedExpansionAll.toGridInput
    (h : TrackBCompleteCanonicalUnnormalizedExpansionAll)
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) :
    TrackBCompleteCanonicalUnnormalizedExpansionInput endpoint mesh where
  sum_repr := by
    intro j m _hm omega
    simpa [trackBGridErrorCanonicalSupport] using
      h.sum_repr_all omega (endpoint j m + 1)

/-- The summatory square-smoothing theorem supplies the normalized canonical
complete expansion for any Track B grid. -/
noncomputable def trackBCompleteCanonicalExpansionInput_of_squareSmoothing
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) :
    TrackBCompleteCanonicalExpansionInput endpoint mesh :=
  (trackBCompleteCanonicalUnnormalizedExpansionAll_of_squareSmoothing
    |>.toGridInput endpoint mesh).toExpansionInput

/-- The complete canonical expansion supplies the canonical error
representation by subtracting the squarefree critical approximation. -/
noncomputable def TrackBCompleteCanonicalExpansionInput.toErrorRepresentationInput
    {endpoint : ℕ → ℕ → ℕ} {mesh : ℕ → ℕ}
    (h : TrackBCompleteCanonicalExpansionInput endpoint mesh) :
    TrackBGridErrorCanonicalRepresentationInput endpoint mesh where
  repr := by
    intro j m hm omega
    exact
      trackBError_eq_canonicalWeightedSum_of_normSum_eq omega
        (endpoint j m) (h.norm_repr j m hm omega)

/-- The canonical representation alone now supplies the canonical moment
input. -/
noncomputable def TrackBGridErrorCanonicalRepresentationInput.toCanonicalMomentInput
    {endpoint : ℕ → ℕ → ℕ} {mesh : ℕ → ℕ}
    (h : TrackBGridErrorCanonicalRepresentationInput endpoint mesh) :
    TrackBGridErrorCanonicalMomentInput endpoint mesh where
  repr := h.repr
  coeff_abs_le := by
    intro j m d _hm hd
    exact
      trackBGridErrorCanonicalWeight_abs_le
        (trackBGridErrorCanonicalSupport_pos hd)

/-- The canonical representation alone supplies the squarefree moment input
with budget `1`. -/
noncomputable def TrackBGridErrorCanonicalRepresentationInput.toSquarefreeMomentInput
    {endpoint : ℕ → ℕ → ℕ} {mesh : ℕ → ℕ}
    (h : TrackBGridErrorCanonicalRepresentationInput endpoint mesh) :
    TrackBGridErrorSquarefreeMomentInput endpoint mesh (fun _ _ => 1) :=
  h.toCanonicalMomentInput.toSquarefreeMomentInput

/-- The summatory square-smoothing theorem supplies the canonical Track B
grid-error representation for any grid. -/
noncomputable def trackBGridErrorCanonicalRepresentationInput_of_squareSmoothing
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) :
    TrackBGridErrorCanonicalRepresentationInput endpoint mesh :=
  (trackBCompleteCanonicalExpansionInput_of_squareSmoothing endpoint mesh)
    |>.toErrorRepresentationInput

/-- The summatory square-smoothing theorem supplies the canonical Track B
grid-error moment input with budget `1`. -/
noncomputable def trackBGridErrorSquarefreeMomentInput_of_squareSmoothing
    (endpoint : ℕ → ℕ → ℕ) (mesh : ℕ → ℕ) :
    TrackBGridErrorSquarefreeMomentInput endpoint mesh (fun _ _ => 1) :=
  (trackBGridErrorCanonicalRepresentationInput_of_squareSmoothing endpoint mesh)
    |>.toSquarefreeMomentInput

/-- Deterministic rough reciprocal mass input.  This is the Lean-facing target
for the sieve/Mertens estimate

```text
sum_{e^X < b <= e^{X+L}, b squarefree, P^-(b)>e^Lambda} 1/b
  asymp L / Lambda.
```

It is not a probability event by itself; it is consumed by the deterministic
squarefree block implication that turns the product, boundary, flat, degree,
prefix-martingale replacement, and Gaussian good events into a crossing. -/
structure TrackBRoughReciprocalMassInput (mesh : ℕ → ℕ) where
  mass : ℕ → ℕ → ℝ
  lower : ℕ → ℕ → ℝ
  upper : ℕ → ℕ → ℝ
  lower_le_mass :
    ∀ j r, r ∈ Finset.Icc 1 (mesh j) → lower j r ≤ mass j r
  mass_le_upper :
    ∀ j r, r ∈ Finset.Icc 1 (mesh j) → mass j r ≤ upper j r

/-- Reciprocal mass of a finite rough component set. -/
noncomputable def trackBRoughReciprocalMassOn (S : Finset ℕ) : ℝ :=
  ∑ b ∈ S, ((b : ℝ)⁻¹)

theorem trackBRoughReciprocalMassOn_nonneg (S : Finset ℕ) :
    0 ≤ trackBRoughReciprocalMassOn S := by
  unfold trackBRoughReciprocalMassOn
  exact Finset.sum_nonneg fun b _hb =>
    inv_nonneg.mpr (Nat.cast_nonneg b)

theorem trackBRoughReciprocalMassOn_mono
    {S T : Finset ℕ} (hST : S ⊆ T) :
    trackBRoughReciprocalMassOn S ≤ trackBRoughReciprocalMassOn T := by
  unfold trackBRoughReciprocalMassOn
  exact
    Finset.sum_le_sum_of_subset_of_nonneg hST
      (by
        intro b _hbT _hbS
        exact inv_nonneg.mpr (Nat.cast_nonneg b))

@[simp] theorem trackBRoughReciprocalMassOn_empty :
    trackBRoughReciprocalMassOn ∅ = 0 := by
  simp [trackBRoughReciprocalMassOn]

theorem trackBRoughReciprocalMassOn_union
    {S T : Finset ℕ} (hdisj : Disjoint S T) :
    trackBRoughReciprocalMassOn (S ∪ T) =
      trackBRoughReciprocalMassOn S + trackBRoughReciprocalMassOn T := by
  unfold trackBRoughReciprocalMassOn
  exact Finset.sum_union hdisj

/-- If every element of `S` is at least `L`, its reciprocal mass is bounded by
`|S| / L`. -/
theorem trackBRoughReciprocalMassOn_le_card_mul_inv
    {S : Finset ℕ} {L : ℕ} (hLpos : 0 < L)
    (hL : ∀ b, b ∈ S → L ≤ b) :
    trackBRoughReciprocalMassOn S ≤ (S.card : ℝ) * ((L : ℝ)⁻¹) := by
  unfold trackBRoughReciprocalMassOn
  calc
    ∑ b ∈ S, ((b : ℝ)⁻¹)
        ≤ ∑ b ∈ S, ((L : ℝ)⁻¹) := by
          refine Finset.sum_le_sum ?_
          intro b hb
          have hLr : 0 < (L : ℝ) := by exact_mod_cast hLpos
          have hle : (L : ℝ) ≤ (b : ℝ) := by exact_mod_cast hL b hb
          exact inv_anti₀ hLr hle
    _ = (S.card : ℝ) * ((L : ℝ)⁻¹) := by
          simp [mul_comm]

/-- If every element of `S` is positive and at most `U`, its reciprocal mass is
bounded below by `|S| / U`. -/
theorem card_mul_inv_le_trackBRoughReciprocalMassOn
    {S : Finset ℕ} {U : ℕ} (hpos : ∀ b, b ∈ S → 0 < b)
    (hU : ∀ b, b ∈ S → b ≤ U) :
    (S.card : ℝ) * ((U : ℝ)⁻¹) ≤
      trackBRoughReciprocalMassOn S := by
  unfold trackBRoughReciprocalMassOn
  calc
    (S.card : ℝ) * ((U : ℝ)⁻¹)
        = ∑ b ∈ S, ((U : ℝ)⁻¹) := by
          simp [mul_comm]
    _ ≤ ∑ b ∈ S, ((b : ℝ)⁻¹) := by
          refine Finset.sum_le_sum ?_
          intro b hb
          have hbpos : 0 < (b : ℝ) := by exact_mod_cast hpos b hb
          have hle : (b : ℝ) ≤ (U : ℝ) := by exact_mod_cast hU b hb
          exact inv_anti₀ hbpos hle

/-- `n` has no prime factor at most the roughness cutoff `y`. -/
def IsYRough (y n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → y < p

/-- Roughness passes to divisors. -/
theorem IsYRough.of_dvd {y m n : ℕ}
    (hrough : IsYRough y n) (hmn : m ∣ n) :
    IsYRough y m := by
  intro p hp hpm
  exact hrough p hp (dvd_trans hpm hmn)

/-- A product of two `y`-rough integers is `y`-rough. -/
theorem IsYRough.mul {y a b : ℕ}
    (ha : IsYRough y a) (hb : IsYRough y b) :
    IsYRough y (a * b) := by
  intro p hp hpab
  rcases hp.dvd_mul.mp hpab with hpa | hpb
  · exact ha p hp hpa
  · exact hb p hp hpb

/-- If a product is `y`-rough, then its left factor is `y`-rough. -/
theorem IsYRough.left_of_mul {y a b : ℕ}
    (h : IsYRough y (a * b)) :
    IsYRough y a :=
  h.of_dvd (Nat.dvd_mul_right a b)

/-- If a product is `y`-rough, then its right factor is `y`-rough. -/
theorem IsYRough.right_of_mul {y a b : ℕ}
    (h : IsYRough y (a * b)) :
    IsYRough y b :=
  h.of_dvd (Nat.dvd_mul_left b a)

/-- Concrete finite rough interval `(lo, hi]`, restricted to squarefree
integers all of whose prime factors are larger than `y`. -/
noncomputable def trackBRoughIntervalSet
    (lo hi y : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc (lo + 1) hi).filter fun b =>
    Squarefree b ∧ IsYRough y b

theorem mem_trackBRoughIntervalSet
    {lo hi y b : ℕ} :
    b ∈ trackBRoughIntervalSet lo hi y ↔
      lo < b ∧ b ≤ hi ∧ Squarefree b ∧ IsYRough y b := by
  classical
  unfold trackBRoughIntervalSet
  rw [Finset.mem_filter]
  constructor
  · intro h
    rcases h with ⟨hbIcc, hsf, hrough⟩
    rcases Finset.mem_Icc.mp hbIcc with ⟨hlo, hhi⟩
    exact ⟨Nat.lt_of_succ_le hlo, hhi, hsf, hrough⟩
  · rintro ⟨hlo, hhi, hsf, hrough⟩
    exact ⟨Finset.mem_Icc.mpr ⟨Nat.succ_le_of_lt hlo, hhi⟩, hsf, hrough⟩

theorem isYRough_mono {y₁ y₂ n : ℕ}
    (hy : y₂ ≤ y₁) (hrough : IsYRough y₁ n) :
    IsYRough y₂ n := by
  intro p hp hpn
  exact lt_of_le_of_lt hy (hrough p hp hpn)

/-- Enlarging the interval and lowering the roughness cutoff enlarges the
rough interval set. -/
theorem trackBRoughIntervalSet_subset_of_bounds
    {lo₁ hi₁ y₁ lo₂ hi₂ y₂ : ℕ}
    (hlo : lo₂ ≤ lo₁) (hhi : hi₁ ≤ hi₂) (hy : y₂ ≤ y₁) :
    trackBRoughIntervalSet lo₁ hi₁ y₁ ⊆
      trackBRoughIntervalSet lo₂ hi₂ y₂ := by
  intro b hb
  rw [mem_trackBRoughIntervalSet] at hb ⊢
  rcases hb with ⟨hlo₁, hhi₁, hsf, hrough⟩
  exact ⟨lt_of_le_of_lt hlo hlo₁, le_trans hhi₁ hhi, hsf,
    isYRough_mono hy hrough⟩

theorem trackBRoughIntervalSet_bounds
    {lo hi y b : ℕ} (hb : b ∈ trackBRoughIntervalSet lo hi y) :
    lo < b ∧ b ≤ hi := by
  rw [mem_trackBRoughIntervalSet] at hb
  exact ⟨hb.1, hb.2.1⟩

theorem trackBRoughIntervalSet_squarefree
    {lo hi y b : ℕ} (hb : b ∈ trackBRoughIntervalSet lo hi y) :
    Squarefree b := by
  rw [mem_trackBRoughIntervalSet] at hb
  exact hb.2.2.1

theorem trackBRoughIntervalSet_rough
    {lo hi y b : ℕ} (hb : b ∈ trackBRoughIntervalSet lo hi y) :
    IsYRough y b := by
  rw [mem_trackBRoughIntervalSet] at hb
  exact hb.2.2.2

theorem trackBRoughIntervalMass_le_card_mul_inv_succ_lo
    (lo hi y : ℕ) :
    trackBRoughReciprocalMassOn (trackBRoughIntervalSet lo hi y) ≤
      ((trackBRoughIntervalSet lo hi y).card : ℝ) *
        (((lo + 1 : ℕ) : ℝ)⁻¹) := by
  exact
    trackBRoughReciprocalMassOn_le_card_mul_inv
      (Nat.succ_pos lo)
      (fun b hb => Nat.succ_le_of_lt
        (trackBRoughIntervalSet_bounds hb).1)

theorem card_mul_inv_hi_le_trackBRoughIntervalMass
    (lo hi y : ℕ) :
    ((trackBRoughIntervalSet lo hi y).card : ℝ) * (((hi : ℕ) : ℝ)⁻¹) ≤
      trackBRoughReciprocalMassOn (trackBRoughIntervalSet lo hi y) := by
  exact
    card_mul_inv_le_trackBRoughReciprocalMassOn
      (fun b hb => lt_of_le_of_lt (Nat.zero_le lo)
        (trackBRoughIntervalSet_bounds hb).1)
      (fun b hb => (trackBRoughIntervalSet_bounds hb).2)

/-- Concrete finite-set version of the rough reciprocal mass certificate. -/
structure TrackBRoughReciprocalMassSetCertificate (mesh : ℕ → ℕ) where
  bSet : ℕ → ℕ → Finset ℕ
  lower : ℕ → ℕ → ℝ
  upper : ℕ → ℕ → ℝ
  lower_le_mass :
    ∀ j r, r ∈ Finset.Icc 1 (mesh j) →
      lower j r ≤ trackBRoughReciprocalMassOn (bSet j r)
  mass_le_upper :
    ∀ j r, r ∈ Finset.Icc 1 (mesh j) →
      trackBRoughReciprocalMassOn (bSet j r) ≤ upper j r

/-- Finite-set rough mass certificates specialize to the abstract rough mass
input used by the Track B analytic certificate. -/
noncomputable def TrackBRoughReciprocalMassSetCertificate.toInput
    {mesh : ℕ → ℕ}
    (h : TrackBRoughReciprocalMassSetCertificate mesh) :
    TrackBRoughReciprocalMassInput mesh where
  mass := fun j r => trackBRoughReciprocalMassOn (h.bSet j r)
  lower := h.lower
  upper := h.upper
  lower_le_mass := h.lower_le_mass
  mass_le_upper := h.mass_le_upper

/-- Interval-endpoint version of the rough reciprocal mass certificate.  The
analytic sieve/Mertens theorem should supply the two mass inequalities for
these concrete sets. -/
structure TrackBRoughIntervalMassCertificate (mesh : ℕ → ℕ) where
  lo : ℕ → ℕ → ℕ
  hi : ℕ → ℕ → ℕ
  y : ℕ → ℕ
  lower : ℕ → ℕ → ℝ
  upper : ℕ → ℕ → ℝ
  lower_le_mass :
    ∀ j r, r ∈ Finset.Icc 1 (mesh j) →
      lower j r ≤
        trackBRoughReciprocalMassOn
          (trackBRoughIntervalSet (lo j r) (hi j r) (y j))
  mass_le_upper :
    ∀ j r, r ∈ Finset.Icc 1 (mesh j) →
      trackBRoughReciprocalMassOn
          (trackBRoughIntervalSet (lo j r) (hi j r) (y j)) ≤
        upper j r

/-- Concrete rough interval mass certificates specialize to finite-set rough
mass certificates. -/
noncomputable def TrackBRoughIntervalMassCertificate.toSetCertificate
    {mesh : ℕ → ℕ}
    (h : TrackBRoughIntervalMassCertificate mesh) :
    TrackBRoughReciprocalMassSetCertificate mesh where
  bSet := fun j r => trackBRoughIntervalSet (h.lo j r) (h.hi j r) (h.y j)
  lower := h.lower
  upper := h.upper
  lower_le_mass := h.lower_le_mass
  mass_le_upper := h.mass_le_upper

/-- Concrete rough interval mass certificates specialize to the abstract rough
mass input consumed by the finite Track B certificate. -/
noncomputable def TrackBRoughIntervalMassCertificate.toInput
    {mesh : ℕ → ℕ}
    (h : TrackBRoughIntervalMassCertificate mesh) :
    TrackBRoughReciprocalMassInput mesh :=
  h.toSetCertificate.toInput

/-- Cardinality version of the rough interval estimate.

This is often the convenient output of a finite sieve/counting lemma.  The
endpoint reciprocal bounds above convert it into the reciprocal-mass interface
used by the Track B finite block. -/
structure TrackBRoughIntervalCardinalityCertificate (mesh : ℕ → ℕ) where
  lo : ℕ → ℕ → ℕ
  hi : ℕ → ℕ → ℕ
  y : ℕ → ℕ
  lowerCard : ℕ → ℕ → ℝ
  upperCard : ℕ → ℕ → ℝ
  lower_le_card :
    ∀ j r, r ∈ Finset.Icc 1 (mesh j) →
      lowerCard j r ≤
        ((trackBRoughIntervalSet (lo j r) (hi j r) (y j)).card : ℝ)
  card_le_upper :
    ∀ j r, r ∈ Finset.Icc 1 (mesh j) →
      ((trackBRoughIntervalSet (lo j r) (hi j r) (y j)).card : ℝ) ≤
        upperCard j r

/-- Cardinality rough interval certificates imply reciprocal-mass rough
interval certificates by bounding every reciprocal between the endpoint
reciprocals. -/
noncomputable def TrackBRoughIntervalCardinalityCertificate.toMassCertificate
    {mesh : ℕ → ℕ}
    (h : TrackBRoughIntervalCardinalityCertificate mesh) :
    TrackBRoughIntervalMassCertificate mesh where
  lo := h.lo
  hi := h.hi
  y := h.y
  lower := fun j r => h.lowerCard j r * (((h.hi j r : ℕ) : ℝ)⁻¹)
  upper := fun j r => h.upperCard j r * ((((h.lo j r + 1 : ℕ) : ℝ))⁻¹)
  lower_le_mass := by
    intro j r hr
    calc
      h.lowerCard j r * (((h.hi j r : ℕ) : ℝ)⁻¹)
          ≤
        ((trackBRoughIntervalSet (h.lo j r) (h.hi j r) (h.y j)).card : ℝ) *
          (((h.hi j r : ℕ) : ℝ)⁻¹) := by
          exact mul_le_mul_of_nonneg_right (h.lower_le_card j r hr)
            (inv_nonneg.mpr (Nat.cast_nonneg _))
      _ ≤
        trackBRoughReciprocalMassOn
          (trackBRoughIntervalSet (h.lo j r) (h.hi j r) (h.y j)) := by
          exact card_mul_inv_hi_le_trackBRoughIntervalMass
            (h.lo j r) (h.hi j r) (h.y j)
  mass_le_upper := by
    intro j r hr
    calc
      trackBRoughReciprocalMassOn
          (trackBRoughIntervalSet (h.lo j r) (h.hi j r) (h.y j))
          ≤
        ((trackBRoughIntervalSet (h.lo j r) (h.hi j r) (h.y j)).card : ℝ) *
          ((((h.lo j r + 1 : ℕ) : ℝ))⁻¹) := by
          exact trackBRoughIntervalMass_le_card_mul_inv_succ_lo
            (h.lo j r) (h.hi j r) (h.y j)
      _ ≤ h.upperCard j r * ((((h.lo j r + 1 : ℕ) : ℝ))⁻¹) := by
          exact mul_le_mul_of_nonneg_right (h.card_le_upper j r hr)
            (inv_nonneg.mpr (Nat.cast_nonneg _))

/-- Cardinality rough interval certificates specialize all the way to the
abstract rough reciprocal-mass input consumed by the finite Track B
certificate. -/
noncomputable def TrackBRoughIntervalCardinalityCertificate.toInput
    {mesh : ℕ → ℕ}
    (h : TrackBRoughIntervalCardinalityCertificate mesh) :
    TrackBRoughReciprocalMassInput mesh :=
  h.toMassCertificate.toInput

/-- Build the six Track B finite bad events from the component events and
finite error variables. -/
def trackBFiniteBadEventsOf
    (mesh : ℕ → ℕ)
    (productBad mooBad gaussianBad : ℕ → Set Omega)
    (boundaryThreshold flatThreshold degreeThreshold : ℕ → ℝ)
    (boundaryEnergy : Fin 2 → ℕ → ℕ → Omega → ℝ)
    (flatTail degreeTail : ℕ → ℕ → Omega → ℝ) :
    TrackBFiniteBadEvents
  | ⟨0, _⟩, j => productBad j
  | ⟨1, _⟩, j =>
      trackBTwoSidedMeshAbove mesh boundaryThreshold boundaryEnergy j
  | ⟨2, _⟩, j =>
      trackBMeshPartialSumDeviation mesh flatThreshold flatTail j
  | ⟨3, _⟩, j =>
      trackBMeshPartialSumDeviation mesh degreeThreshold degreeTail j
  | ⟨4, _⟩, j => mooBad j
  | ⟨5, _⟩, j => gaussianBad j

/-- A component-wise finite-core certificate.  This is the current most
concrete Lean-facing Track B target.

The deterministic field `squarefree_failure_subset_bad` is where the
decomposition

```text
Z_r = Y_r + B_r + Z_r^flat
Y_r -> Y_r^(<=D)
```

is used: if product, boundary, flat, degree, prefix-martingale replacement,
and Gaussian good events all hold, the squarefree block must cross the
required level.
-/
structure TrackBFiniteCoreComponentCertificate extends
    TrackBFiniteCoreToCompleteCertificate where
  productBad : ℕ → Set Omega
  mooBad : ℕ → Set Omega
  gaussianBad : ℕ → Set Omega
  boundaryThreshold : ℕ → ℝ
  flatThreshold : ℕ → ℝ
  degreeThreshold : ℕ → ℝ
  boundaryEnergy : Fin 2 → ℕ → ℕ → Omega → ℝ
  boundaryUpper : Fin 2 → ℕ → ℕ → ℝ
  flatTail : ℕ → ℕ → Omega → ℝ
  flatPartialSecond : ℕ → ℕ → ℝ
  degreeTail : ℕ → ℕ → Omega → ℝ
  degreePartialSecond : ℕ → ℕ → ℝ
  product_prob : ∀ j, mu (productBad j) ≤ errProduct j
  moo_prob : ∀ j, mu (mooBad j) ≤ errMOO j
  gaussian_prob : ∀ j, mu (gaussianBad j) ≤ errGaussian j
  boundary_threshold_pos : ∀ j, 0 < boundaryThreshold j
  boundary_integrable :
    ∀ side j r, r ∈ Finset.Icc 1 (mesh j) →
      Integrable (fun omega => boundaryEnergy side j r omega) mu
  boundary_nonneg :
    ∀ side j r, r ∈ Finset.Icc 1 (mesh j) →
      0 ≤ᵐ[mu] fun omega => boundaryEnergy side j r omega
  boundary_mean :
    ∀ side j r, r ∈ Finset.Icc 1 (mesh j) →
      (∫ omega, boundaryEnergy side j r omega ∂mu) ≤
        boundaryUpper side j r
  boundary_budget_le :
    ∀ j,
      trackBTwoSidedMeshFirstMomentBudget mesh boundaryThreshold
        boundaryUpper j ≤ errBoundary j
  flat_threshold_pos : ∀ j, 0 < flatThreshold j
  flat_integrable :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      Integrable
        (fun omega => (trackBMeshPartialSum flatTail j m omega) ^ 2) mu
  flat_second :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      (∫ omega, (trackBMeshPartialSum flatTail j m omega) ^ 2 ∂mu) ≤
        flatPartialSecond j m
  flat_budget_le :
    ∀ j,
      trackBMeshPartialSumSecondMomentBudget mesh flatThreshold
        flatPartialSecond j ≤ errFlat j
  degree_threshold_pos : ∀ j, 0 < degreeThreshold j
  degree_integrable :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      Integrable
        (fun omega => (trackBMeshPartialSum degreeTail j m omega) ^ 2) mu
  degree_second :
    ∀ j m, m ∈ Finset.Icc 1 (mesh j) →
      (∫ omega, (trackBMeshPartialSum degreeTail j m omega) ^ 2 ∂mu) ≤
        degreePartialSecond j m
  degree_budget_le :
    ∀ j,
      trackBMeshPartialSumSecondMomentBudget mesh degreeThreshold
        degreePartialSecond j ≤ errDegree j
  squarefree_failure_subset_bad :
    ∀ j,
      trackBSquarefreeBlockFailure 0 endpoint mesh B j ⊆
        trackBFiniteCoreBadUnion
          (trackBFiniteBadEventsOf mesh productBad mooBad gaussianBad
            boundaryThreshold flatThreshold degreeThreshold boundaryEnergy
            flatTail degreeTail) j

/-- The component certificate supplies the probability estimate for each of
the six finite bad events. -/
theorem TrackBFiniteCoreComponentCertificate.bad_prob
    (h : TrackBFiniteCoreComponentCertificate) :
    ∀ i j,
      mu
          (trackBFiniteBadEventsOf h.mesh h.productBad h.mooBad h.gaussianBad
            h.boundaryThreshold h.flatThreshold h.degreeThreshold
            h.boundaryEnergy h.flatTail h.degreeTail i j) ≤
        trackBFiniteErrorBudgetOf h.errProduct h.errBoundary h.errFlat
          h.errDegree h.errMOO h.errGaussian i j := by
  intro i j
  fin_cases i
  · simpa [trackBFiniteBadEventsOf, trackBFiniteErrorBudgetOf] using
      h.product_prob j
  · simpa [trackBFiniteBadEventsOf, trackBFiniteErrorBudgetOf] using
      (measure_trackBTwoSidedMeshAbove_le_firstMomentBudget h.mesh
        h.boundaryThreshold h.boundaryEnergy h.boundaryUpper
        h.boundary_threshold_pos h.boundary_integrable h.boundary_nonneg
        h.boundary_mean j).trans (h.boundary_budget_le j)
  · simpa [trackBFiniteBadEventsOf, trackBFiniteErrorBudgetOf] using
      (measure_trackBMeshPartialSumDeviation_le_secondMomentBudget h.mesh
        h.flatThreshold h.flatTail h.flatPartialSecond
        h.flat_threshold_pos h.flat_integrable h.flat_second j).trans
        (h.flat_budget_le j)
  · simpa [trackBFiniteBadEventsOf, trackBFiniteErrorBudgetOf] using
      (measure_trackBMeshPartialSumDeviation_le_secondMomentBudget h.mesh
        h.degreeThreshold h.degreeTail h.degreePartialSecond
        h.degree_threshold_pos h.degree_integrable h.degree_second j).trans
        (h.degree_budget_le j)
  · simpa [trackBFiniteBadEventsOf, trackBFiniteErrorBudgetOf] using
      h.moo_prob j
  · simpa [trackBFiniteBadEventsOf, trackBFiniteErrorBudgetOf] using
      h.gaussian_prob j

/-- Component-wise finite-core certificates are event-level finite-core
certificates. -/
noncomputable def trackBFiniteCoreEventCertificate_of_componentCertificate
    (h : TrackBFiniteCoreComponentCertificate) :
    TrackBFiniteCoreEventCertificate where
  params := h.params
  endpoint := h.endpoint
  mesh := h.mesh
  level := h.level
  B := h.B
  A := h.A
  errorSecond := h.errorSecond
  errProduct := h.errProduct
  errBoundary := h.errBoundary
  errFlat := h.errFlat
  errDegree := h.errDegree
  errMOO := h.errMOO
  errGaussian := h.errGaussian
  B_pos := h.B_pos
  A_pos := h.A_pos
  A_le_quarter_B := h.A_le_quarter_B
  level_le_half_B := h.level_le_half_B
  endpoint_tendsto_atTop := h.endpoint_tendsto_atTop
  level_tendsto_atTop := h.level_tendsto_atTop
  B_tendsto_atTop := h.B_tendsto_atTop
  error_second_integrable := h.error_second_integrable
  error_second_upper := h.error_second_upper
  fail_summable := h.fail_summable
  prob_squarefree_block_fail := h.prob_squarefree_block_fail
  bad :=
    trackBFiniteBadEventsOf h.mesh h.productBad h.mooBad h.gaussianBad
      h.boundaryThreshold h.flatThreshold h.degreeThreshold h.boundaryEnergy
      h.flatTail h.degreeTail
  squarefree_failure_subset_bad := h.squarefree_failure_subset_bad
  bad_prob := h.bad_prob

/-- Direct closure from the component-wise finite-core certificate. -/
theorem erdos1144_of_trackBFiniteCoreComponentCertificate
    (h : TrackBFiniteCoreComponentCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBFiniteCoreEventCertificate
    (trackBFiniteCoreEventCertificate_of_componentCertificate h)

/-!
## Named analytic input certificate

This layer is the next inward-facing Track B target.  It separates the seven
remaining analytic ingredients:

* small-prime product event;
* deterministic rough reciprocal mass;
* boundary first-moment control;
* flat Rankin/Menshov control;
* degree-cutoff Rankin/Menshov control;
* prefix martingale lower-orthant replacement;
* Gaussian crossing.

The theorem below is purely wiring: these named inputs produce the already
checked component certificate.
-/

/-- Track B finite analytic certificate with the remaining inputs named
separately. -/
structure TrackBFiniteAnalyticCertificate extends
    TrackBFiniteCoreToCompleteCertificate where
  product : TrackBDirectProbabilityInput errProduct
  roughMass : TrackBRoughReciprocalMassInput mesh
  boundary : TrackBBoundaryMomentInput mesh errBoundary
  flat : TrackBPartialSecondMomentInput mesh errFlat
  degreeTailInput : TrackBPartialSecondMomentInput mesh errDegree
  moo : TrackBDirectProbabilityInput errMOO
  gaussian : TrackBDirectProbabilityInput errGaussian
  squarefree_failure_subset_bad :
    ∀ j,
      trackBSquarefreeBlockFailure 0 endpoint mesh B j ⊆
        trackBFiniteCoreBadUnion
          (trackBFiniteBadEventsOf mesh product.bad moo.bad gaussian.bad
            boundary.threshold flat.threshold degreeTailInput.threshold
            boundary.energy flat.tail degreeTailInput.tail) j

/-- Named analytic certificates specialize to the component-wise finite-core
certificate. -/
noncomputable def trackBFiniteCoreComponentCertificate_of_analyticCertificate
    (h : TrackBFiniteAnalyticCertificate) :
    TrackBFiniteCoreComponentCertificate where
  toTrackBFiniteCoreToCompleteCertificate :=
    h.toTrackBFiniteCoreToCompleteCertificate
  productBad := h.product.bad
  mooBad := h.moo.bad
  gaussianBad := h.gaussian.bad
  boundaryThreshold := h.boundary.threshold
  flatThreshold := h.flat.threshold
  degreeThreshold := h.degreeTailInput.threshold
  boundaryEnergy := h.boundary.energy
  boundaryUpper := h.boundary.upper
  flatTail := h.flat.tail
  flatPartialSecond := h.flat.partialSecond
  degreeTail := h.degreeTailInput.tail
  degreePartialSecond := h.degreeTailInput.partialSecond
  product_prob := h.product.prob
  moo_prob := h.moo.prob
  gaussian_prob := h.gaussian.prob
  boundary_threshold_pos := h.boundary.threshold_pos
  boundary_integrable := h.boundary.integrable
  boundary_nonneg := h.boundary.nonneg
  boundary_mean := h.boundary.mean
  boundary_budget_le := h.boundary.budget_le
  flat_threshold_pos := h.flat.threshold_pos
  flat_integrable := h.flat.integrable
  flat_second := h.flat.second
  flat_budget_le := h.flat.budget_le
  degree_threshold_pos := h.degreeTailInput.threshold_pos
  degree_integrable := h.degreeTailInput.integrable
  degree_second := h.degreeTailInput.second
  degree_budget_le := h.degreeTailInput.budget_le
  squarefree_failure_subset_bad := h.squarefree_failure_subset_bad

/-- Direct closure from the named analytic finite Track B certificate. -/
theorem erdos1144_of_trackBFiniteAnalyticCertificate
    (h : TrackBFiniteAnalyticCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBFiniteCoreComponentCertificate
    (trackBFiniteCoreComponentCertificate_of_analyticCertificate h)

/-!
## Concrete-pieces analytic certificate

This is the most concrete finite Track B interface currently available.  It
uses the three-piece small-prime product certificate, finite rough reciprocal
mass sets, and squarefree-weighted representations for the flat and degree
tails.
-/

/-- Concrete-pieces version of the finite analytic certificate. -/
structure TrackBFiniteAnalyticPiecesCertificate extends
    TrackBFiniteCoreToCompleteCertificate where
  productPiece : TrackBSmallPrimeProductCertificate errProduct
  roughMassPiece : TrackBRoughReciprocalMassSetCertificate mesh
  boundary : TrackBBoundaryMomentInput mesh errBoundary
  flatPiece : TrackBSquarefreeTailSecondMomentCertificate mesh errFlat
  degreePiece : TrackBSquarefreeTailSecondMomentCertificate mesh errDegree
  moo : TrackBDirectProbabilityInput errMOO
  gaussian : TrackBDirectProbabilityInput errGaussian
  squarefree_failure_subset_bad :
    ∀ j,
      trackBSquarefreeBlockFailure 0 endpoint mesh B j ⊆
        trackBFiniteCoreBadUnion
          (trackBFiniteBadEventsOf mesh
            (trackBSmallPrimeProductBad productPiece.fullProduct
              productPiece.truncatedProduct productPiece.lower
              productPiece.upper productPiece.truncTolerance)
            moo.bad gaussian.bad boundary.threshold flatPiece.threshold
            degreePiece.threshold boundary.energy flatPiece.tail
            degreePiece.tail) j

/-- Concrete-pieces certificates specialize to the named analytic certificate. -/
noncomputable def trackBFiniteAnalyticCertificate_of_piecesCertificate
    (h : TrackBFiniteAnalyticPiecesCertificate) :
    TrackBFiniteAnalyticCertificate where
  toTrackBFiniteCoreToCompleteCertificate :=
    h.toTrackBFiniteCoreToCompleteCertificate
  product := h.productPiece.toDirectProbabilityInput
  roughMass := h.roughMassPiece.toInput
  boundary := h.boundary
  flat := h.flatPiece.toPartialSecondMomentInput
  degreeTailInput := h.degreePiece.toPartialSecondMomentInput
  moo := h.moo
  gaussian := h.gaussian
  squarefree_failure_subset_bad := h.squarefree_failure_subset_bad

/-- Direct closure from the concrete-pieces Track B finite certificate. -/
theorem erdos1144_of_trackBFiniteAnalyticPiecesCertificate
    (h : TrackBFiniteAnalyticPiecesCertificate) :
    Erdos1144 :=
  erdos1144_of_trackBFiniteAnalyticCertificate
    (trackBFiniteAnalyticCertificate_of_piecesCertificate h)

/-!
## Fully concrete finite Track B pieces

This final adapter names the current intended finite inputs directly:

* the three-piece small-prime product certificate;
* concrete rough interval reciprocal mass;
* boundary, flat, and degree moment certificates;
* prefix-vector martingale lower-orthant replacement;
* the three-term Gaussian crossing certificate.

It exists to keep the public proof obligation close to the current paper plan
while reusing the already checked finite-core closure spine.
-/

/-- Most concrete finite Track B certificate currently exposed by the Lean
interface.  The inherited `errGaussian` slot is allowed to dominate the
explicit three-term Gaussian crossing budget. -/
structure TrackBFiniteConcretePiecesCertificate
    (etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞) extends
    TrackBFiniteCoreToCompleteCertificate where
  gaussian_budget_le :
    ∀ j,
      trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j ≤
        errGaussian j
  productPiece : TrackBSmallPrimeProductCertificate errProduct
  roughInterval : TrackBRoughIntervalMassCertificate mesh
  boundary : TrackBBoundaryMomentInput mesh errBoundary
  flatPiece : TrackBSquarefreeTailSecondMomentCertificate mesh errFlat
  degreePiece : TrackBSquarefreeTailSecondMomentCertificate mesh errDegree
  prefixMartingale : TrackBPrefixMartingaleReplacementCertificate errMOO
  gaussianCrossing :
    TrackBGaussianCrossingCertificate etaTerm meshTerm varianceTerm
  squarefree_failure_subset_bad :
    ∀ j,
      trackBSquarefreeBlockFailure 0 endpoint mesh B j ⊆
        trackBFiniteCoreBadUnion
          (trackBFiniteBadEventsOf mesh
            (trackBSmallPrimeProductBad productPiece.fullProduct
              productPiece.truncatedProduct productPiece.lower
              productPiece.upper productPiece.truncTolerance)
            prefixMartingale.bad gaussianCrossing.bad boundary.threshold
            flatPiece.threshold degreePiece.threshold boundary.energy
            flatPiece.tail degreePiece.tail) j

/-- The fully concrete finite pieces specialize to the previous concrete-pieces
certificate. -/
noncomputable def trackBFiniteAnalyticPiecesCertificate_of_concretePieces
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    (h : TrackBFiniteConcretePiecesCertificate etaTerm meshTerm varianceTerm) :
    TrackBFiniteAnalyticPiecesCertificate where
  toTrackBFiniteCoreToCompleteCertificate :=
    h.toTrackBFiniteCoreToCompleteCertificate
  productPiece := h.productPiece
  roughMassPiece := h.roughInterval.toSetCertificate
  boundary := h.boundary
  flatPiece := h.flatPiece
  degreePiece := h.degreePiece
  moo := h.prefixMartingale.toDirectProbabilityInput
  gaussian :=
    h.gaussianCrossing.toDirectProbabilityInputLe h.gaussian_budget_le
  squarefree_failure_subset_bad := h.squarefree_failure_subset_bad

/-- Direct closure from the fully concrete finite Track B pieces. -/
theorem erdos1144_of_trackBFiniteConcretePiecesCertificate
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    (h : TrackBFiniteConcretePiecesCertificate etaTerm meshTerm varianceTerm) :
    Erdos1144 :=
  erdos1144_of_trackBFiniteAnalyticPiecesCertificate
    (trackBFiniteAnalyticPiecesCertificate_of_concretePieces h)

/-- Variant of the fully concrete Track B certificate where the rough-number
input is supplied as a finite cardinality estimate rather than a reciprocal
mass estimate.  The already-proved endpoint reciprocal bounds convert this to
the mass interface automatically. -/
structure TrackBFiniteConcreteCardinalityPiecesCertificate
    (etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞) extends
    TrackBFiniteCoreToCompleteCertificate where
  gaussian_budget_le :
    ∀ j,
      trackBGaussianCrossingBudget etaTerm meshTerm varianceTerm j ≤
        errGaussian j
  productPiece : TrackBSmallPrimeProductCertificate errProduct
  roughCardinality : TrackBRoughIntervalCardinalityCertificate mesh
  boundary : TrackBBoundaryMomentInput mesh errBoundary
  flatPiece : TrackBSquarefreeTailSecondMomentCertificate mesh errFlat
  degreePiece : TrackBSquarefreeTailSecondMomentCertificate mesh errDegree
  prefixMartingale : TrackBPrefixMartingaleReplacementCertificate errMOO
  gaussianCrossing :
    TrackBGaussianCrossingCertificate etaTerm meshTerm varianceTerm
  squarefree_failure_subset_bad :
    ∀ j,
      trackBSquarefreeBlockFailure 0 endpoint mesh B j ⊆
        trackBFiniteCoreBadUnion
          (trackBFiniteBadEventsOf mesh
            (trackBSmallPrimeProductBad productPiece.fullProduct
              productPiece.truncatedProduct productPiece.lower
              productPiece.upper productPiece.truncTolerance)
            prefixMartingale.bad gaussianCrossing.bad boundary.threshold
            flatPiece.threshold degreePiece.threshold boundary.energy
            flatPiece.tail degreePiece.tail) j

/-- Cardinality-piece certificates specialize to the reciprocal-mass concrete
Track B certificate. -/
noncomputable def trackBFiniteConcretePiecesCertificate_of_cardinalityPieces
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    (h :
      TrackBFiniteConcreteCardinalityPiecesCertificate
        etaTerm meshTerm varianceTerm) :
    TrackBFiniteConcretePiecesCertificate etaTerm meshTerm varianceTerm where
  toTrackBFiniteCoreToCompleteCertificate :=
    h.toTrackBFiniteCoreToCompleteCertificate
  gaussian_budget_le := h.gaussian_budget_le
  productPiece := h.productPiece
  roughInterval := h.roughCardinality.toMassCertificate
  boundary := h.boundary
  flatPiece := h.flatPiece
  degreePiece := h.degreePiece
  prefixMartingale := h.prefixMartingale
  gaussianCrossing := h.gaussianCrossing
  squarefree_failure_subset_bad := h.squarefree_failure_subset_bad

/-- Direct closure from the finite Track B certificate whose rough input is a
cardinality estimate. -/
theorem erdos1144_of_trackBFiniteConcreteCardinalityPiecesCertificate
    {etaTerm meshTerm varianceTerm : ℕ → ℝ≥0∞}
    (h :
      TrackBFiniteConcreteCardinalityPiecesCertificate
        etaTerm meshTerm varianceTerm) :
    Erdos1144 :=
  erdos1144_of_trackBFiniteConcretePiecesCertificate
    (trackBFiniteConcretePiecesCertificate_of_cardinalityPieces h)

end Problem1144
end Erdos
