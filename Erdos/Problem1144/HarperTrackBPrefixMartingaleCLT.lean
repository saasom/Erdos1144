import Erdos.Problem1144.Model

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem1144

/-!
# Prefix-vector martingale CLT interface for Track B

The finite Track B block theorem only tests one event: a running maximum of
partial sums.  Instead of exposing an arbitrary convex-set invariance theorem,
this file records the sharper interface we actually need: lower-orthant
approximation for the prefix vector.

The arithmetic rough-core layer should eventually provide Walsh coefficients
for the increment vector `Y`.  The probabilistic replacement theorem should be
stated for

```text
prefixVec Y = (Y_0, Y_0 + Y_1, ..., Y_0 + ... + Y_m, ...),
```

tested against lower orthants.  The crossing event is exactly the preimage of
one lower orthant under this prefix map.
-/

/-- Prefix sum through index `m`, using the natural order on `Fin M`. -/
noncomputable def prefixSum {M : ℕ} (x : Fin M → ℝ) (m : Fin M) : ℝ :=
  ∑ r : Fin M, if (r : ℕ) ≤ (m : ℕ) then x r else 0

/-- Prefix-vector map attached to an increment vector. -/
noncomputable def prefixVec {M : ℕ} (x : Fin M → ℝ) : Fin M → ℝ :=
  fun m => prefixSum x m

/-- Lower orthant with coordinate-wise strict upper barriers. -/
def lowerOrthant {M : ℕ} (b : Fin M → ℝ) : Set (Fin M → ℝ) :=
  {s | ∀ m : Fin M, s m < b m}

/-- Running-maximum lower crossing event in increment coordinates. -/
def crossingSet {M : ℕ} (a : ℝ) : Set (Fin M → ℝ) :=
  {x | prefixVec x ∈ lowerOrthant (fun _ => a)}

theorem mem_lowerOrthant_iff {M : ℕ} {b s : Fin M → ℝ} :
    s ∈ lowerOrthant b ↔ ∀ m : Fin M, s m < b m := by
  rfl

theorem mem_crossingSet_iff {M : ℕ} {a : ℝ} {x : Fin M → ℝ} :
    x ∈ crossingSet a ↔ ∀ m : Fin M, prefixSum x m < a := by
  rfl

/-- A lower-orthant approximation certificate for a random vector `S`.

In the intended use, `S` is already the prefix vector of the rough-core
increments and `γ` is the matching Gaussian law. -/
structure LowerOrthantApprox
    {Ω' : Type*} [MeasurableSpace Ω'] {M : ℕ}
    (μ' : Measure Ω') (S : Ω' → Fin M → ℝ)
    (γ : Measure (Fin M → ℝ)) (ε : ℝ) : Prop where
  bound :
    ∀ b : Fin M → ℝ,
      |((μ' {ω | S ω ∈ lowerOrthant b}).toReal) -
        ((γ (lowerOrthant b)).toReal)| ≤ ε

/-- Lower-orthant approximation is monotone in the error tolerance. -/
theorem LowerOrthantApprox.mono
    {Ω' : Type*} [MeasurableSpace Ω'] {M : ℕ}
    {μ' : Measure Ω'} {S : Ω' → Fin M → ℝ}
    {γ : Measure (Fin M → ℝ)} {ε ε' : ℝ}
    (h : LowerOrthantApprox μ' S γ ε) (hε : ε ≤ ε') :
    LowerOrthantApprox μ' S γ ε' where
  bound := fun b => (h.bound b).trans hε

/-- Lower-orthant approximation for the prefix vector immediately gives the
crossing-event approximation. -/
theorem crossing_of_lowerOrthantApprox
    {Ω' : Type*} [MeasurableSpace Ω'] {M : ℕ}
    (μ' : Measure Ω') (Y : Ω' → Fin M → ℝ)
    (γ : Measure (Fin M → ℝ)) (a ε : ℝ)
    (h :
      LowerOrthantApprox μ'
        (fun ω => prefixVec (Y ω))
        γ ε) :
    |((μ' {ω | Y ω ∈ crossingSet a}).toReal) -
      ((γ (lowerOrthant (fun _ : Fin M => a))).toReal)| ≤ ε := by
  simpa [crossingSet] using h.bound (fun _ : Fin M => a)

/-!
## Walsh-coefficient placeholders

The next layer will represent rough-core coordinates by finite Walsh
coefficients.  Keeping these definitions in this module makes the martingale
CLT theorem stateable as finite coefficient inequalities rather than as an
opaque "MOO convex replacement" axiom.
-/

/-- Finite Walsh-vector coefficient table, with an explicit degree cap. -/
structure WalshVec
    (Q I : Type*) [Fintype Q] [DecidableEq Q] [Fintype I]
    (D : ℕ) where
  coeff : I → Finset Q → ℝ
  degree_le : ∀ i A, coeff i A ≠ 0 → A.card ≤ D

/-- Directional coefficient of one Walsh character. -/
noncomputable def dirCoeff
    {Q I : Type*} [Fintype Q] [DecidableEq Q] [Fintype I]
    (c : I → Finset Q → ℝ) (u : I → ℝ) (A : Finset Q) : ℝ :=
  ∑ i : I, u i * c i A

/-- Directional Walsh variance, omitting the constant coefficient. -/
noncomputable def dirVar
    {Q I : Type*} [Fintype Q] [DecidableEq Q] [Fintype I]
    (c : I → Finset Q → ℝ) (u : I → ℝ) : ℝ :=
  ∑ A : Finset Q, if A = ∅ then 0 else (dirCoeff c u A) ^ 2

/-- Prefix coefficients for the prefix-vector process. -/
noncomputable def prefixCoeff
    {Q : Type*} [Fintype Q] [DecidableEq Q] {M : ℕ}
    (c : Fin M → Finset Q → ℝ) (m : Fin M) (A : Finset Q) : ℝ :=
  ∑ r : Fin M, if (r : ℕ) ≤ (m : ℕ) then c r A else 0

/-- Prefixing a Walsh coefficient table preserves the same degree cap. -/
noncomputable def WalshVec.prefix
    {Q : Type*} [Fintype Q] [DecidableEq Q] {M D : ℕ}
    (w : WalshVec Q (Fin M) D) : WalshVec Q (Fin M) D where
  coeff := prefixCoeff w.coeff
  degree_le := by
    intro m A hne
    by_contra hcard
    have hzero : ∀ r : Fin M, w.coeff r A = 0 := by
      intro r
      by_contra hr
      exact hcard (w.degree_le r A hr)
    have hsum :
        prefixCoeff w.coeff m A = 0 := by
      unfold prefixCoeff
      simp [hzero]
    exact hne hsum

/-- Adjoint of the prefix-sum map on finite vectors.  If `u` tests the prefix
vector, `prefixAdjoint u` is the corresponding linear functional on increment
coordinates. -/
noncomputable def prefixAdjoint {M : ℕ} (u : Fin M → ℝ) : Fin M → ℝ :=
  fun r => ∑ m : Fin M, if (r : ℕ) ≤ (m : ℕ) then u m else 0

/-- Walsh character on a finite Boolean cube. -/
noncomputable def walshChar
    {Q : Type*} [DecidableEq Q]
    (omega : Q → Bool) (A : Finset Q) : ℝ :=
  ∏ q ∈ A, boolSign (omega q)

@[simp] theorem boolSign_not (b : Bool) :
    boolSign (!b) = - boolSign b := by
  cases b <;> simp [boolSign]

@[simp] theorem walshChar_empty
    {Q : Type*} [DecidableEq Q] (omega : Q → Bool) :
    walshChar omega (∅ : Finset Q) = 1 := by
  simp [walshChar]

theorem walshChar_mul_self
    {Q : Type*} [DecidableEq Q]
    (omega : Q → Bool) (A : Finset Q) :
    walshChar omega A * walshChar omega A = 1 := by
  unfold walshChar
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_eq_one fun q _hq => by
    cases omega q <;> simp [boolSign]

@[simp] theorem walshChar_sq
    {Q : Type*} [DecidableEq Q]
    (omega : Q → Bool) (A : Finset Q) :
    walshChar omega A ^ 2 = 1 := by
  rw [pow_two, walshChar_mul_self]

/-- Flip one Boolean coordinate. -/
def boolFlipAt {Q : Type*} [DecidableEq Q]
    (q : Q) (omega : Q → Bool) : Q → Bool :=
  fun r => if r = q then !omega r else omega r

@[simp] theorem boolFlipAt_self
    {Q : Type*} [DecidableEq Q] (q : Q) (omega : Q → Bool) :
    boolFlipAt q omega q = !omega q := by
  simp [boolFlipAt]

@[simp] theorem boolFlipAt_of_ne
    {Q : Type*} [DecidableEq Q] {q r : Q} (omega : Q → Bool)
    (h : r ≠ q) :
    boolFlipAt q omega r = omega r := by
  simp [boolFlipAt, h]

/-- Flipping the same coordinate twice is the identity equivalence. -/
def boolFlipAtEquiv {Q : Type*} [DecidableEq Q]
    (q : Q) : (Q → Bool) ≃ (Q → Bool) where
  toFun := boolFlipAt q
  invFun := boolFlipAt q
  left_inv := by
    intro omega
    funext r
    by_cases h : r = q
    · subst h
      simp [boolFlipAt]
    · simp [boolFlipAt, h]
  right_inv := by
    intro omega
    funext r
    by_cases h : r = q
    · subst h
      simp [boolFlipAt]
    · simp [boolFlipAt, h]

theorem walshChar_boolFlipAt_of_notMem
    {Q : Type*} [DecidableEq Q]
    {q : Q} {A : Finset Q} (omega : Q → Bool)
    (hq : q ∉ A) :
    walshChar (boolFlipAt q omega) A = walshChar omega A := by
  unfold walshChar
  refine Finset.prod_congr rfl ?_
  intro r hr
  have hrq : r ≠ q := by
    intro h
    exact hq (by simpa [h] using hr)
  simp [boolFlipAt, hrq]

theorem walshChar_boolFlipAt_of_mem
    {Q : Type*} [DecidableEq Q]
    {q : Q} {A : Finset Q} (omega : Q → Bool)
    (hq : q ∈ A) :
    walshChar (boolFlipAt q omega) A = - walshChar omega A := by
  classical
  unfold walshChar
  rw [← Finset.mul_prod_erase A (fun r => boolSign (boolFlipAt q omega r)) hq]
  rw [← Finset.mul_prod_erase A (fun r => boolSign (omega r)) hq]
  have hprod :
      (∏ x ∈ A.erase q, boolSign (boolFlipAt q omega x)) =
        ∏ x ∈ A.erase q, boolSign (omega x) := by
    refine Finset.prod_congr rfl ?_
    intro x hx
    have hxne : x ≠ q := Finset.ne_of_mem_erase hx
    simp [boolFlipAt, hxne]
  rw [hprod]
  simp [boolFlipAt]

/-- Evaluation of a finite Walsh coefficient vector on a finite Boolean cube. -/
noncomputable def evalWalshVec
    {Q I : Type*} [Fintype Q] [DecidableEq Q] [Fintype I]
    (c : I → Finset Q → ℝ) (omega : Q → Bool) (i : I) : ℝ :=
  ∑ A : Finset Q, c i A * walshChar omega A

theorem prefixCoeff_eq_prefixSum
    {Q : Type*} [Fintype Q] [DecidableEq Q] {M : ℕ}
    (c : Fin M → Finset Q → ℝ) (m : Fin M) (A : Finset Q) :
    prefixCoeff c m A = prefixSum (fun r : Fin M => c r A) m := by
  rfl

/-- Directional coefficients of prefix coefficients are directional
coefficients of the original increments against the adjoint direction. -/
theorem dirCoeff_prefixCoeff
    {Q : Type*} [Fintype Q] [DecidableEq Q] {M : ℕ}
    (c : Fin M → Finset Q → ℝ) (u : Fin M → ℝ) (A : Finset Q) :
    dirCoeff (prefixCoeff c) u A =
      dirCoeff c (prefixAdjoint u) A := by
  classical
  unfold dirCoeff prefixCoeff prefixAdjoint
  calc
    ∑ i : Fin M,
        u i * (∑ r : Fin M, if (r : ℕ) ≤ (i : ℕ) then c r A else 0)
        =
      ∑ i : Fin M, ∑ r : Fin M,
        u i * (if (r : ℕ) ≤ (i : ℕ) then c r A else 0) := by
        refine Finset.sum_congr rfl ?_
        intro i _hi
        rw [Finset.mul_sum]
    _ =
      ∑ r : Fin M, ∑ i : Fin M,
        u i * (if (r : ℕ) ≤ (i : ℕ) then c r A else 0) := by
        rw [Finset.sum_comm]
    _ =
      ∑ r : Fin M,
        (∑ i : Fin M, if (r : ℕ) ≤ (i : ℕ) then u i else 0) * c r A := by
        refine Finset.sum_congr rfl ?_
        intro r _hr
        calc
          ∑ i : Fin M,
              u i * (if (r : ℕ) ≤ (i : ℕ) then c r A else 0)
              =
            ∑ i : Fin M,
              (if (r : ℕ) ≤ (i : ℕ) then u i else 0) * c r A := by
              refine Finset.sum_congr rfl ?_
              intro i _hi
              by_cases hri : (r : ℕ) ≤ (i : ℕ) <;> simp [hri]
          _ =
            (∑ i : Fin M, if (r : ℕ) ≤ (i : ℕ) then u i else 0) *
              c r A := by
              rw [Finset.sum_mul]
    _ =
      ∑ r : Fin M,
        ((∑ m : Fin M, if (r : ℕ) ≤ (m : ℕ) then u m else 0) *
          c r A) := by
        rfl

/-- Directional variances of prefix coefficients are the increment directional
variances against the adjoint direction. -/
theorem dirVar_prefixCoeff
    {Q : Type*} [Fintype Q] [DecidableEq Q] {M : ℕ}
    (c : Fin M → Finset Q → ℝ) (u : Fin M → ℝ) :
    dirVar (prefixCoeff c) u =
      dirVar c (prefixAdjoint u) := by
  classical
  unfold dirVar
  refine Finset.sum_congr rfl ?_
  intro A _hA
  by_cases hA : A = ∅
  · simp [hA]
  · simp [hA, dirCoeff_prefixCoeff c u A]

/-- Evaluating prefix coefficients is the same as taking the prefix vector
after evaluating the original coefficients. -/
theorem evalWalshVec_prefixCoeff
    {Q : Type*} [Fintype Q] [DecidableEq Q] {M : ℕ}
    (c : Fin M → Finset Q → ℝ) (omega : Q → Bool) (m : Fin M) :
    evalWalshVec (prefixCoeff c) omega m =
      prefixSum (fun r : Fin M => evalWalshVec c omega r) m := by
  classical
  unfold evalWalshVec prefixCoeff prefixSum
  calc
    ∑ A : Finset Q,
        (∑ r : Fin M, if (r : ℕ) ≤ (m : ℕ) then c r A else 0) *
          walshChar omega A
        =
      ∑ A : Finset Q, ∑ r : Fin M,
        (if (r : ℕ) ≤ (m : ℕ) then c r A else 0) * walshChar omega A := by
        refine Finset.sum_congr rfl ?_
        intro A _hA
        rw [Finset.sum_mul]
    _ =
      ∑ r : Fin M, ∑ A : Finset Q,
        (if (r : ℕ) ≤ (m : ℕ) then c r A else 0) * walshChar omega A := by
        rw [Finset.sum_comm]
    _ =
      ∑ r : Fin M,
        if (r : ℕ) ≤ (m : ℕ) then
          ∑ A : Finset Q, c r A * walshChar omega A
        else
          0 := by
        refine Finset.sum_congr rfl ?_
        intro r _hr
        by_cases hrm : (r : ℕ) ≤ (m : ℕ)
        · simp [hrm]
        · simp [hrm]

theorem dirVar_nonneg
    {Q I : Type*} [Fintype Q] [DecidableEq Q] [Fintype I]
    (c : I → Finset Q → ℝ) (u : I → ℝ) :
    0 ≤ dirVar c u := by
  classical
  unfold dirVar
  exact Finset.sum_nonneg fun A _hA => by
    by_cases hA : A = ∅
    · simp [hA]
    · simp [hA, sq_nonneg]

/-!
## Ordered martingale coefficient contracts

For the rough-core application the sign coordinates are revealed in a fixed
order.  The coefficient of the `q`-th martingale difference is the part of a
Walsh monomial whose largest newly revealed coordinate is `q`.

The key point is directional: low influence must hold for every linear
combination of the prefix vector, not only coordinate-by-coordinate.
-/

/-- All coordinates in `B` are revealed before `q`. -/
def before {N : ℕ} (q : Fin N) (B : Finset (Fin N)) : Prop :=
  ∀ r ∈ B, (r : ℕ) < (q : ℕ)

/-- Walsh coefficient of the `q`-th martingale amplitude. -/
noncomputable def martCoeff
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (q : Fin N) (i : I) (B : Finset (Fin N)) : ℝ := by
  classical
  exact if before q B ∧ q ∉ B then c i (insert q B) else 0

/-- Directional variance contribution of one martingale difference. -/
noncomputable def dirMartVarAt
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (q : Fin N) (u : I → ℝ) : ℝ :=
  ∑ B : Finset (Fin N),
    (∑ i : I, u i * martCoeff c q i B) ^ 2

theorem dirMartVarAt_nonneg
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (q : Fin N) (u : I → ℝ) :
    0 ≤ dirMartVarAt c q u := by
  unfold dirMartVarAt
  exact Finset.sum_nonneg fun B _hB => sq_nonneg _

/-- Directional martingale amplitudes for prefix coefficients are directional
martingale amplitudes of the original coefficients against the adjoint
direction. -/
theorem dirMartCoeff_prefixCoeff
    {N M : ℕ}
    (c : Fin M → Finset (Fin N) → ℝ)
    (q : Fin N) (u : Fin M → ℝ) (B : Finset (Fin N)) :
    (∑ i : Fin M, u i * martCoeff (prefixCoeff c) q i B) =
      ∑ i : Fin M, (prefixAdjoint u) i * martCoeff c q i B := by
  classical
  unfold martCoeff prefixCoeff prefixAdjoint
  by_cases hcond : before q B ∧ q ∉ B
  · simp only [hcond]
    calc
      ∑ i : Fin M,
          u i *
            (∑ r : Fin M,
              if (r : ℕ) ≤ (i : ℕ) then c r (insert q B) else 0)
          =
        ∑ i : Fin M, ∑ r : Fin M,
          u i *
            (if (r : ℕ) ≤ (i : ℕ) then c r (insert q B) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Finset.mul_sum]
      _ =
        ∑ r : Fin M, ∑ i : Fin M,
          u i *
            (if (r : ℕ) ≤ (i : ℕ) then c r (insert q B) else 0) := by
          rw [Finset.sum_comm]
      _ =
        ∑ r : Fin M,
          (∑ i : Fin M, if (r : ℕ) ≤ (i : ℕ) then u i else 0) *
            c r (insert q B) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          calc
            ∑ i : Fin M,
                u i *
                  (if (r : ℕ) ≤ (i : ℕ) then c r (insert q B) else 0)
                =
              ∑ i : Fin M,
                (if (r : ℕ) ≤ (i : ℕ) then u i else 0) *
                  c r (insert q B) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                by_cases hri : (r : ℕ) ≤ (i : ℕ) <;> simp [hri]
            _ =
              (∑ i : Fin M, if (r : ℕ) ≤ (i : ℕ) then u i else 0) *
                c r (insert q B) := by
                rw [Finset.sum_mul]
      _ =
        ∑ r : Fin M,
          (∑ m : Fin M, if (r : ℕ) ≤ (m : ℕ) then u m else 0) *
            c r (insert q B) := by
          rfl
  · simp [hcond]

/-- Martingale variance contributions for prefix coefficients reduce to the
original coefficients tested against the prefix adjoint direction. -/
theorem dirMartVarAt_prefixCoeff
    {N M : ℕ}
    (c : Fin M → Finset (Fin N) → ℝ)
    (q : Fin N) (u : Fin M → ℝ) :
    dirMartVarAt (prefixCoeff c) q u =
      dirMartVarAt c q (prefixAdjoint u) := by
  classical
  unfold dirMartVarAt martCoeff prefixCoeff prefixAdjoint
  refine Finset.sum_congr rfl ?_
  intro B _hB
  by_cases hcond : before q B ∧ q ∉ B
  · simp only [hcond]
    congr 1
    calc
      ∑ i : Fin M,
          u i *
            (∑ r : Fin M,
              if (r : ℕ) ≤ (i : ℕ) then c r (insert q B) else 0)
          =
        ∑ i : Fin M, ∑ r : Fin M,
          u i *
            (if (r : ℕ) ≤ (i : ℕ) then c r (insert q B) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro i _hi
          rw [Finset.mul_sum]
      _ =
        ∑ r : Fin M, ∑ i : Fin M,
          u i *
            (if (r : ℕ) ≤ (i : ℕ) then c r (insert q B) else 0) := by
          rw [Finset.sum_comm]
      _ =
        ∑ r : Fin M,
          (∑ i : Fin M, if (r : ℕ) ≤ (i : ℕ) then u i else 0) *
            c r (insert q B) := by
          refine Finset.sum_congr rfl ?_
          intro r _hr
          calc
            ∑ i : Fin M,
                u i *
                  (if (r : ℕ) ≤ (i : ℕ) then c r (insert q B) else 0)
                =
              ∑ i : Fin M,
                (if (r : ℕ) ≤ (i : ℕ) then u i else 0) *
                  c r (insert q B) := by
                refine Finset.sum_congr rfl ?_
                intro i _hi
                by_cases hri : (r : ℕ) ≤ (i : ℕ) <;> simp [hri]
            _ =
              (∑ i : Fin M, if (r : ℕ) ≤ (i : ℕ) then u i else 0) *
                c r (insert q B) := by
                rw [Finset.sum_mul]
      _ =
        ∑ r : Fin M,
          (∑ m : Fin M, if (r : ℕ) ≤ (m : ℕ) then u m else 0) *
            c r (insert q B) := by
          rfl
  · simp [hcond]

/-- Directional low-influence condition for the ordered martingale
decomposition. -/
def DirectionalInfluenceBound
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (τ : ℝ) : Prop :=
  ∀ q : Fin N, ∀ u : I → ℝ,
    dirMartVarAt c q u ≤ τ * dirVar c u

/-- The directional influence condition is monotone in the tolerance. -/
theorem DirectionalInfluenceBound.mono
    {N : ℕ} {I : Type*} [Fintype I]
    {c : I → Finset (Fin N) → ℝ} {τ τ' : ℝ}
    (h : DirectionalInfluenceBound c τ) (hτ : τ ≤ τ') :
    DirectionalInfluenceBound c τ' := by
  intro q u
  exact (h q u).trans (mul_le_mul_of_nonneg_right hτ (dirVar_nonneg c u))

/-- Directional influence for increment coefficients implies directional
influence for prefix coefficients with the same tolerance. -/
theorem DirectionalInfluenceBound.prefixCoeff
    {N M : ℕ} {c : Fin M → Finset (Fin N) → ℝ} {τ : ℝ}
    (h : DirectionalInfluenceBound c τ) :
    DirectionalInfluenceBound (prefixCoeff c) τ := by
  intro q u
  rw [dirMartVarAt_prefixCoeff, dirVar_prefixCoeff]
  exact h q (prefixAdjoint u)

/-- Symmetric difference of two finite coordinate sets. -/
def finsetSymmDiff {α : Type*} [DecidableEq α]
    (A B : Finset α) : Finset α :=
  (A \ B) ∪ (B \ A)

theorem mem_finsetSymmDiff
    {α : Type*} [DecidableEq α] {A B : Finset α} {a : α} :
    a ∈ finsetSymmDiff A B ↔ (a ∈ A ∧ a ∉ B) ∨ (a ∈ B ∧ a ∉ A) := by
  simp [finsetSymmDiff]

theorem walshChar_mul_boolFlipAt_of_symmDiff_mem
    {Q : Type*} [DecidableEq Q]
    {q : Q} {A B : Finset Q} (omega : Q → Bool)
    (hq : q ∈ finsetSymmDiff A B) :
    walshChar (boolFlipAt q omega) A *
        walshChar (boolFlipAt q omega) B =
      -(walshChar omega A * walshChar omega B) := by
  rcases (mem_finsetSymmDiff).mp hq with ⟨hqA, hqB⟩ | ⟨hqB, hqA⟩
  · rw [walshChar_boolFlipAt_of_mem omega hqA,
      walshChar_boolFlipAt_of_notMem omega hqB]
    ring
  · rw [walshChar_boolFlipAt_of_notMem omega hqA,
      walshChar_boolFlipAt_of_mem omega hqB]
    ring

theorem finsetSymmDiff_comm
    {α : Type*} [DecidableEq α] (A B : Finset α) :
    finsetSymmDiff A B = finsetSymmDiff B A := by
  ext a
  simp [mem_finsetSymmDiff, and_comm, or_comm]

theorem finsetSymmDiff_self
    {α : Type*} [DecidableEq α] (A : Finset α) :
    finsetSymmDiff A A = ∅ := by
  ext a
  simp [mem_finsetSymmDiff]

theorem finsetSymmDiff_eq_empty_iff
    {α : Type*} [DecidableEq α] {A B : Finset α} :
    finsetSymmDiff A B = ∅ ↔ A = B := by
  constructor
  · intro h
    ext a
    constructor
    · intro ha
      by_contra hb
      have hmem : a ∈ finsetSymmDiff A B :=
        (mem_finsetSymmDiff).mpr (Or.inl ⟨ha, hb⟩)
      simp [h] at hmem
    · intro hb
      by_contra ha
      have hmem : a ∈ finsetSymmDiff A B :=
        (mem_finsetSymmDiff).mpr (Or.inr ⟨hb, ha⟩)
      simp [h] at hmem
  · intro h
    rw [h, finsetSymmDiff_self]

/-- A Walsh-character product has zero finite-cube sum when the two
characters are distinct.  The proof pairs cube points by flipping a coordinate
where the two character supports differ. -/
theorem sum_walshChar_mul_eq_zero_of_ne
    {Q : Type*} [Fintype Q] [DecidableEq Q]
    {A B : Finset Q} (hAB : A ≠ B) :
    (∑ omega : Q → Bool, walshChar omega A * walshChar omega B) = 0 := by
  classical
  have hsdiff : finsetSymmDiff A B ≠ ∅ := by
    intro hzero
    exact hAB ((finsetSymmDiff_eq_empty_iff).mp hzero)
  rcases Finset.nonempty_iff_ne_empty.mpr hsdiff with ⟨q, hq⟩
  let S : ℝ := ∑ omega : Q → Bool, walshChar omega A * walshChar omega B
  have hperm :
      (∑ omega : Q → Bool,
          walshChar (boolFlipAt q omega) A *
            walshChar (boolFlipAt q omega) B) = S := by
    change
      (∑ omega : Q → Bool,
          walshChar (boolFlipAt q omega) A *
            walshChar (boolFlipAt q omega) B)
        =
      ∑ omega : Q → Bool, walshChar omega A * walshChar omega B
    exact
      Fintype.sum_equiv
        (boolFlipAtEquiv q)
        (fun omega : Q → Bool =>
          walshChar (boolFlipAt q omega) A *
            walshChar (boolFlipAt q omega) B)
        (fun omega : Q → Bool =>
          walshChar omega A * walshChar omega B)
        (fun _ => rfl)
  have hneg :
      (∑ omega : Q → Bool,
          walshChar (boolFlipAt q omega) A *
            walshChar (boolFlipAt q omega) B) = -S := by
    unfold S
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro omega _homega
    exact walshChar_mul_boolFlipAt_of_symmDiff_mem omega hq
  have hS : S = -S := hperm.symm.trans hneg
  linarith

theorem finsetSymmDiff_empty_right
    {α : Type*} [DecidableEq α] (A : Finset α) :
    finsetSymmDiff A ∅ = A := by
  ext a
  simp [mem_finsetSymmDiff]

theorem finsetSymmDiff_empty_left
    {α : Type*} [DecidableEq α] (A : Finset α) :
    finsetSymmDiff ∅ A = A := by
  rw [finsetSymmDiff_comm, finsetSymmDiff_empty_right]

/-- Reindex finite subsets not containing `q` by inserting `q`.  This is the
basic bookkeeping step behind the constant Malliavin covariance coefficient:
`B ↦ insert q B` is a bijection from subsets avoiding `q` to subsets
containing `q`. -/
theorem sum_insert_notMem_finset
    {α : Type*} [Fintype α] [DecidableEq α]
    (q : α) (f : Finset α → ℝ) :
    (∑ B : Finset α, if q ∉ B then f (insert q B) else 0) =
      ∑ A : Finset α, if q ∈ A then f A else 0 := by
  classical
  let s : Finset (Finset α) :=
    (Finset.univ.filter fun B : Finset α => q ∉ B)
  let t : Finset (Finset α) :=
    (Finset.univ.filter fun A : Finset α => q ∈ A)
  calc
    (∑ B : Finset α, if q ∉ B then f (insert q B) else 0)
        = ∑ B ∈ s, f (insert q B) := by
          simp [s, Finset.sum_filter]
    _ = ∑ A ∈ t, f A := by
          refine
            Finset.sum_bij
              (fun B _hB => insert q B) ?_ ?_ ?_ ?_
          · intro B hB
            simp [t]
          · intro B₁ hB₁ B₂ hB₂ hEq
            have hnot₁ : q ∉ B₁ := by simpa [s] using hB₁
            have hnot₂ : q ∉ B₂ := by simpa [s] using hB₂
            have hErase := congrArg (fun A : Finset α => A.erase q) hEq
            simpa [hnot₁, hnot₂] using hErase
          · intro A hA
            have hmem : q ∈ A := by simpa [t] using hA
            refine ⟨A.erase q, ?_, ?_⟩
            · simp [s]
            · simp [hmem]
          · intro B _hB
            rfl
    _ = ∑ A : Finset α, if q ∈ A then f A else 0 := by
          simp [t, Finset.sum_filter]

/-- Averaging a constant over the members of a finite set cancels the
cardinality denominator, with the empty set handled separately. -/
theorem sum_mem_div_card_eq
    {α : Type*} [Fintype α] [DecidableEq α]
    (A : Finset α) (x : ℝ) :
    (∑ q : α, if q ∈ A then x / (A.card : ℝ) else 0) =
      if A = ∅ then 0 else x := by
  classical
  by_cases hA : A = ∅
  · simp [hA]
  · have hcardNat : A.card ≠ 0 := by
      exact Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hA)
    have hcardReal : (A.card : ℝ) ≠ 0 := by exact_mod_cast hcardNat
    calc
      (∑ q : α, if q ∈ A then x / (A.card : ℝ) else 0)
          = ∑ q ∈ A, x / (A.card : ℝ) := by
            rw [← Finset.sum_filter]
            simp
      _ = A.card • (x / (A.card : ℝ)) := by
            rw [Finset.sum_const]
      _ = x := by
            rw [nsmul_eq_mul]
            field_simp [hcardReal]
      _ = (if A = ∅ then 0 else x) := by
            simp [hA]

/-- Walsh coefficient of the predictable quadratic-variation bilinear form. -/
noncomputable def qvCoeff
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (u v : I → ℝ) (T : Finset (Fin N)) : ℝ :=
  ∑ q : Fin N,
    ∑ B : Finset (Fin N),
      ∑ C : Finset (Fin N),
        if finsetSymmDiff B C = T then
          (∑ i : I, u i * martCoeff c q i B) *
            (∑ i : I, v i * martCoeff c q i C)
        else
          0

theorem qvCoeff_comm
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (u v : I → ℝ) (T : Finset (Fin N)) :
    qvCoeff c u v T = qvCoeff c v u T := by
  classical
  unfold qvCoeff
  refine Finset.sum_congr rfl ?_
  intro q _hq
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro B _hB
  refine Finset.sum_congr rfl ?_
  intro C _hC
  by_cases h : finsetSymmDiff C B = T
  · have h' : finsetSymmDiff B C = T := by
      simpa [finsetSymmDiff_comm] using h
    simp [h, h', mul_comm]
  · have h' : finsetSymmDiff B C ≠ T := by
      intro hBC
      exact h (by simpa [finsetSymmDiff_comm] using hBC)
    simp [h, h']

/-- Predictable quadratic-variation coefficients for prefix coefficients are
the original QV coefficients tested against adjoint directions. -/
theorem qvCoeff_prefixCoeff
    {N M : ℕ}
    (c : Fin M → Finset (Fin N) → ℝ)
    (u v : Fin M → ℝ) (T : Finset (Fin N)) :
    qvCoeff (prefixCoeff c) u v T =
      qvCoeff c (prefixAdjoint u) (prefixAdjoint v) T := by
  classical
  unfold qvCoeff
  refine Finset.sum_congr rfl ?_
  intro q _hq
  refine Finset.sum_congr rfl ?_
  intro B _hB
  refine Finset.sum_congr rfl ?_
  intro C _hC
  by_cases h : finsetSymmDiff B C = T
  · simp [h, dirMartCoeff_prefixCoeff c q u B,
      dirMartCoeff_prefixCoeff c q v C]
  · simp [h]

/-- Parseval-style square error of the nonconstant predictable
quadratic-variation coefficients. -/
noncomputable def qvErrorSq
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (u v : I → ℝ) : ℝ :=
  ∑ T : Finset (Fin N), if T = ∅ then 0 else (qvCoeff c u v T) ^ 2

theorem qvErrorSq_nonneg
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (u v : I → ℝ) :
    0 ≤ qvErrorSq c u v := by
  classical
  unfold qvErrorSq
  exact Finset.sum_nonneg fun T _hT => by
    by_cases hT : T = ∅
    · simp [hT]
    · simp [hT, sq_nonneg]

/-- QV square errors for prefix coefficients reduce to increment QV square
errors against adjoint directions. -/
theorem qvErrorSq_prefixCoeff
    {N M : ℕ}
    (c : Fin M → Finset (Fin N) → ℝ) (u v : Fin M → ℝ) :
    qvErrorSq (prefixCoeff c) u v =
      qvErrorSq c (prefixAdjoint u) (prefixAdjoint v) := by
  classical
  unfold qvErrorSq
  refine Finset.sum_congr rfl ?_
  intro T _hT
  by_cases hT : T = ∅
  · simp [hT]
  · simp [hT, qvCoeff_prefixCoeff c u v T]

/-- Directional predictable-quadratic-variation concentration condition. -/
def DirectionalQVBound
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (κ : ℝ) : Prop :=
  ∀ u v : I → ℝ,
    qvErrorSq c u v ≤ κ ^ 2 * dirVar c u * dirVar c v

/-- Directional QV concentration for increment coefficients implies the same
condition for prefix coefficients. -/
theorem DirectionalQVBound.prefixCoeff
    {N M : ℕ} {c : Fin M → Finset (Fin N) → ℝ} {κ : ℝ}
    (h : DirectionalQVBound c κ) :
    DirectionalQVBound (prefixCoeff c) κ := by
  intro u v
  rw [qvErrorSq_prefixCoeff, dirVar_prefixCoeff, dirVar_prefixCoeff]
  exact h (prefixAdjoint u) (prefixAdjoint v)

/-!
## Walsh-Stein coefficient contracts

The refined rough-core Gaussian replacement is a finite-cube
second-order Poincare/Stein theorem for the prefix vector.  The analytic
theorem will use the coefficient quantities below:

* `steinInvCoeff`, the derivative coefficient of `-L^{-1}`;
* `gammaHat`, the Walsh coefficients of the Malliavin/Stein covariance;
* `gammaErrorSq`, the squared nonconstant `L^2` fluctuation of that
  covariance;
* `lambdaCoeff` and `betaCoeff`, the local third-order influence bound.

These are deterministic finite sums.  The later probability theorem can refer
to them directly, rather than to a generic "MOO" or martingale-CLT black box.
-/

/-- Coefficient of the discrete derivative `partial_q` in direction `q`.

If `B = A.erase q` and `q ∈ A`, then the derivative of the Walsh character
`chi_A` contributes the coefficient of `A = insert q B`. -/
noncomputable def walshDerivCoeff
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (q : Fin N) (i : I) (B : Finset (Fin N)) : ℝ := by
  classical
  exact if q ∉ B then c i (insert q B) else 0

@[simp] theorem walshDerivCoeff_of_mem
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    {q : Fin N} {i : I} {B : Finset (Fin N)}
    (hq : q ∈ B) :
    walshDerivCoeff c q i B = 0 := by
  classical
  simp [walshDerivCoeff, hq]

@[simp] theorem walshDerivCoeff_of_notMem
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    {q : Fin N} {i : I} {B : Finset (Fin N)}
    (hq : q ∉ B) :
    walshDerivCoeff c q i B = c i (insert q B) := by
  classical
  simp [walshDerivCoeff, hq]

/-- Coefficient of `partial_q (-L^{-1} S_i)`.

For a nonconstant Walsh character `chi_A`, `-L^{-1}` multiplies the coefficient
by `1 / |A|`.  In derivative coordinates `A = insert q B`. -/
noncomputable def steinInvCoeff
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (q : Fin N) (i : I) (B : Finset (Fin N)) : ℝ := by
  classical
  exact
    if q ∉ B then
      c i (insert q B) / ((insert q B).card : ℝ)
    else
      0

@[simp] theorem steinInvCoeff_of_mem
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    {q : Fin N} {i : I} {B : Finset (Fin N)}
    (hq : q ∈ B) :
    steinInvCoeff c q i B = 0 := by
  classical
  simp [steinInvCoeff, hq]

@[simp] theorem steinInvCoeff_of_notMem
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    {q : Fin N} {i : I} {B : Finset (Fin N)}
    (hq : q ∉ B) :
    steinInvCoeff c q i B =
      c i (insert q B) / ((insert q B).card : ℝ) := by
  classical
  simp [steinInvCoeff, hq]

/-- Evaluation of the discrete derivative `partial_q S_i` from its derivative
coefficient table. -/
noncomputable def walshDerivEval
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (q : Fin N) (omega : Fin N → Bool) (i : I) : ℝ :=
  ∑ B : Finset (Fin N), walshDerivCoeff c q i B * walshChar omega B

/-- Evaluation of `partial_q (-L^{-1} S_i)` from its inverse-generator
derivative coefficient table. -/
noncomputable def steinInvDerivEval
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (q : Fin N) (omega : Fin N → Bool) (i : I) : ℝ :=
  ∑ B : Finset (Fin N), steinInvCoeff c q i B * walshChar omega B

/-- Evaluation of the Malliavin/Stein covariance entry
`Gamma_ij = sum_q partial_q S_i * partial_q (-L^{-1} S_j)`. -/
noncomputable def gammaEval
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (omega : Fin N → Bool) (i j : I) : ℝ :=
  ∑ q : Fin N,
    walshDerivEval c q omega i * steinInvDerivEval c q omega j

/-- Walsh coefficient at character `T` of the Malliavin/Stein covariance
entry

`Gamma_ij = sum_q partial_q S_i * partial_q (-L^{-1} S_j)`.
-/
noncomputable def gammaHat
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (i j : I) (T : Finset (Fin N)) : ℝ :=
  ∑ q : Fin N,
    ∑ B : Finset (Fin N),
      ∑ C : Finset (Fin N),
        if finsetSymmDiff B C = T then
          walshDerivCoeff c q i B * steinInvCoeff c q j C
        else
          0

/-- Walsh covariance matrix entry, written directly from nonconstant
coefficients. -/
noncomputable def walshCovCoeff
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (i j : I) : ℝ :=
  ∑ A : Finset (Fin N), if A = ∅ then 0 else c i A * c j A

theorem walshCovCoeff_comm
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (i j : I) :
    walshCovCoeff c i j = walshCovCoeff c j i := by
  classical
  unfold walshCovCoeff
  refine Finset.sum_congr rfl ?_
  intro A _hA
  by_cases hA : A = ∅
  · simp [hA]
  · simp [hA, mul_comm]

theorem walshCovCoeff_self_nonneg
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (i : I) :
    0 ≤ walshCovCoeff c i i := by
  classical
  unfold walshCovCoeff
  exact Finset.sum_nonneg fun A _hA => by
    by_cases hA : A = ∅
    · simp [hA]
    · simpa [hA] using mul_self_nonneg (c i A)

/-- The constant Walsh coefficient of `Gamma_ij` only receives contributions
from matching derivative characters. -/
theorem gammaHat_empty
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (i j : I) :
    gammaHat c i j ∅ =
      ∑ q : Fin N,
        ∑ B : Finset (Fin N),
          walshDerivCoeff c q i B * steinInvCoeff c q j B := by
  classical
  unfold gammaHat
  refine Finset.sum_congr rfl ?_
  intro q _hq
  refine Finset.sum_congr rfl ?_
  intro B _hB
  simp [finsetSymmDiff_eq_empty_iff]

/-- Constant Malliavin/Stein covariance coefficient after reindexing by the
active coordinate.  The remaining cardinality cancellation is separated into a
later covariance lemma. -/
theorem gammaHat_empty_eq_steinWeightedCov
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (i j : I) :
    gammaHat c i j ∅ =
      ∑ q : Fin N,
        ∑ A : Finset (Fin N),
          if q ∈ A then
            c i A * (c j A / (A.card : ℝ))
          else
            0 := by
  classical
  rw [gammaHat_empty]
  refine Finset.sum_congr rfl ?_
  intro q _hq
  have hleft :
      (∑ B : Finset (Fin N),
          walshDerivCoeff c q i B * steinInvCoeff c q j B)
        =
      ∑ B : Finset (Fin N),
        if q ∉ B then
          c i (insert q B) *
            (c j (insert q B) / ((insert q B).card : ℝ))
        else
          0 := by
    refine Finset.sum_congr rfl ?_
    intro B _hB
    by_cases hqB : q ∈ B
    · simp [hqB]
    · simp [hqB]
  rw [hleft]
  exact
    sum_insert_notMem_finset q
      (fun A : Finset (Fin N) => c i A * (c j A / (A.card : ℝ)))

/-- For each nonempty Walsh character, summing the active-coordinate Stein
weights cancels the `|A|` denominator. -/
theorem sum_mem_stein_weight_eq_covCoeff
    {N : ℕ} (A : Finset (Fin N)) (x y : ℝ) :
    (∑ q : Fin N,
        if q ∈ A then
          x * (y / (A.card : ℝ))
        else
          0) =
      if A = ∅ then 0 else x * y := by
  classical
  calc
    (∑ q : Fin N,
        if q ∈ A then
          x * (y / (A.card : ℝ))
        else
          0)
        =
      ∑ q : Fin N,
        if q ∈ A then
          (x * y) / (A.card : ℝ)
        else
          0 := by
        refine Finset.sum_congr rfl ?_
        intro q _hq
        by_cases hqA : q ∈ A
        · simp [hqA, mul_div_assoc]
        · simp [hqA]
    _ = if A = ∅ then 0 else x * y := by
        exact sum_mem_div_card_eq A (x * y)

/-- The constant Malliavin/Stein covariance coefficient is the Walsh covariance
matrix entry. -/
theorem gammaHat_empty_eq_walshCovCoeff
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (i j : I) :
    gammaHat c i j ∅ = walshCovCoeff c i j := by
  classical
  rw [gammaHat_empty_eq_steinWeightedCov]
  unfold walshCovCoeff
  calc
    (∑ q : Fin N,
        ∑ A : Finset (Fin N),
          if q ∈ A then
            c i A * (c j A / (A.card : ℝ))
          else
            0)
        =
      ∑ A : Finset (Fin N),
        ∑ q : Fin N,
          if q ∈ A then
            c i A * (c j A / (A.card : ℝ))
          else
            0 := by
        rw [Finset.sum_comm]
    _ =
      ∑ A : Finset (Fin N), if A = ∅ then 0 else c i A * c j A := by
        refine Finset.sum_congr rfl ?_
        intro A _hA
        exact sum_mem_stein_weight_eq_covCoeff A (c i A) (c j A)

/-- Uniform average over the finite Boolean cube.  This is the deterministic
finite-cube expectation used in the Parseval/Stein layer. -/
noncomputable def boolCubeAverage
    {N : ℕ} (F : (Fin N → Bool) → ℝ) : ℝ :=
  ((Fintype.card (Fin N → Bool) : ℝ)⁻¹) *
    ∑ omega : Fin N → Bool, F omega

theorem boolCubeAverage_const_one {N : ℕ} :
    boolCubeAverage (N := N) (fun _ => (1 : ℝ)) = 1 := by
  unfold boolCubeAverage
  have hcardNat : Fintype.card (Fin N → Bool) ≠ 0 := Fintype.card_ne_zero
  have hcardReal : (Fintype.card (Fin N → Bool) : ℝ) ≠ 0 := by
    exact_mod_cast hcardNat
  rw [Finset.sum_const]
  rw [nsmul_eq_mul]
  simp only [Finset.card_univ]
  field_simp [hcardReal]

theorem boolCubeAverage_walshChar_mul_of_ne
    {N : ℕ} {A B : Finset (Fin N)} (hAB : A ≠ B) :
    boolCubeAverage
        (fun omega : Fin N → Bool => walshChar omega A * walshChar omega B)
      = 0 := by
  unfold boolCubeAverage
  rw [sum_walshChar_mul_eq_zero_of_ne hAB]
  simp

/-- Finite Boolean-cube orthogonality of Walsh characters. -/
theorem boolCubeAverage_walshChar_mul
    {N : ℕ} (A B : Finset (Fin N)) :
    boolCubeAverage
        (fun omega : Fin N → Bool => walshChar omega A * walshChar omega B)
      =
      if A = B then 1 else 0 := by
  classical
  by_cases hAB : A = B
  · subst hAB
    simpa [walshChar_mul_self] using boolCubeAverage_const_one (N := N)
  · simpa [hAB] using boolCubeAverage_walshChar_mul_of_ne (N := N) (A := A) (B := B) hAB

/-- Pointwise Malliavin/Stein covariance fluctuation after subtracting the
constant Walsh covariance coefficient. -/
noncomputable def gammaFluctuationEval
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (omega : Fin N → Bool) (i j : I) : ℝ :=
  gammaEval c omega i j - walshCovCoeff c i j

/-- Frobenius-square fluctuation of the Malliavin/Stein covariance at one cube
point. -/
noncomputable def gammaFluctuationFrobSq
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (omega : Fin N → Bool) : ℝ :=
  ∑ i : I,
    ∑ j : I,
      (gammaFluctuationEval c omega i j) ^ 2

theorem gammaFluctuationFrobSq_nonneg
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ)
    (omega : Fin N → Bool) :
    0 ≤ gammaFluctuationFrobSq c omega := by
  unfold gammaFluctuationFrobSq
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj => sq_nonneg _

/-- Squared nonconstant Walsh mass of the Malliavin/Stein covariance
fluctuation.  This is the coefficient-level `gammaError^2` used by the
Walsh-Stein lower-orthant replacement theorem. -/
noncomputable def gammaErrorSq
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) : ℝ :=
  ∑ i : I,
    ∑ j : I,
      ∑ T : Finset (Fin N),
        if T = ∅ then 0 else (gammaHat c i j T) ^ 2

theorem gammaErrorSq_nonneg
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) :
    0 ≤ gammaErrorSq c := by
  classical
  unfold gammaErrorSq
  exact Finset.sum_nonneg fun i _hi =>
    Finset.sum_nonneg fun j _hj =>
      Finset.sum_nonneg fun T _hT => by
        by_cases h : T = ∅
        · simp [h]
        · simp [h, sq_nonneg]

/-- Nonnegative square root of the Malliavin/Stein covariance fluctuation. -/
noncomputable def gammaError
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) : ℝ :=
  Real.sqrt (gammaErrorSq c)

theorem gammaError_nonneg
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) :
    0 ≤ gammaError c :=
  Real.sqrt_nonneg _

/-- Local derivative variance for coordinate `i` at rough-prime coordinate
`q`. -/
noncomputable def lambdaCoeff
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (q : Fin N) (i : I) : ℝ :=
  ∑ A : Finset (Fin N), if q ∈ A then (c i A) ^ 2 else 0

theorem lambdaCoeff_nonneg
    {N : ℕ} {I : Type*} [Fintype I]
    (c : I → Finset (Fin N) → ℝ) (q : Fin N) (i : I) :
    0 ≤ lambdaCoeff c q i := by
  classical
  unfold lambdaCoeff
  exact Finset.sum_nonneg fun A _hA => by
    by_cases hq : q ∈ A
    · simp [hq, sq_nonneg]
    · simp [hq]

/-- A deliberately wasteful hypercontractive constant for degree-`D` Walsh
polynomials.  The eventual theorem only needs summability, not sharp constants. -/
noncomputable def hyperConst (D : ℕ) : ℝ :=
  (2 : ℝ) ^ (3 * D)

theorem hyperConst_nonneg (D : ℕ) :
    0 ≤ hyperConst D := by
  unfold hyperConst
  exact pow_nonneg (by norm_num) _

/-- Coefficient-level upper bound for the third-order local influence term in
the Walsh-Stein theorem. -/
noncomputable def betaCoeff
    {N : ℕ} {I : Type*} [Fintype I]
    (D : ℕ) (c : I → Finset (Fin N) → ℝ) : ℝ :=
  hyperConst D *
    ∑ q : Fin N,
      (∑ i : I, Real.sqrt (lambdaCoeff c q i)) ^ 3

theorem betaCoeff_nonneg
    {N : ℕ} {I : Type*} [Fintype I]
    (D : ℕ) (c : I → Finset (Fin N) → ℝ) :
    0 ≤ betaCoeff D c := by
  classical
  unfold betaCoeff
  exact mul_nonneg (hyperConst_nonneg D) <|
    Finset.sum_nonneg fun q _hq =>
      pow_nonneg
        (Finset.sum_nonneg fun i _hi =>
          Real.sqrt_nonneg (lambdaCoeff c q i))
        3

/-- Lean-facing Walsh-Stein lower-orthant certificate.

The eventual finite-cube Stein theorem should construct `lower_orthant` from
the displayed coefficient bounds and the `error_bound`.  Keeping the
coefficient quantities in the certificate makes the analytic assumptions
auditable and gives arithmetic files concrete finite sums to estimate. -/
structure WalshSteinLowerOrthantCertificate
    {Ω' : Type*} [MeasurableSpace Ω'] {N M : ℕ}
    (μ' : Measure Ω')
    (eval : Ω' → Fin M → ℝ)
    (γ : Measure (Fin M → ℝ))
    (c : Fin M → Finset (Fin N) → ℝ)
    (D : ℕ)
    (delta boundaryConst K2 K3 gammaBudget betaBudget ε : ℝ) : Prop where
  gamma_bound : gammaError c ≤ gammaBudget
  beta_bound : betaCoeff D c ≤ betaBudget
  error_bound :
    boundaryConst * delta +
        K2 * (M : ℝ) * gammaBudget / (delta ^ 2) +
          K3 * betaBudget / (delta ^ 3) ≤ ε
  lower_orthant :
    LowerOrthantApprox μ' (fun ω => prefixVec (eval ω)) γ ε

/-- Forget the coefficient bookkeeping and keep the lower-orthant
approximation delivered by the Walsh-Stein certificate. -/
theorem WalshSteinLowerOrthantCertificate.toLowerOrthantApprox
    {Ω' : Type*} [MeasurableSpace Ω'] {N M : ℕ}
    {μ' : Measure Ω'} {eval : Ω' → Fin M → ℝ}
    {γ : Measure (Fin M → ℝ)}
    {c : Fin M → Finset (Fin N) → ℝ}
    {D : ℕ}
    {delta boundaryConst K2 K3 gammaBudget betaBudget ε : ℝ}
    (h :
      WalshSteinLowerOrthantCertificate μ' eval γ c D delta
        boundaryConst K2 K3 gammaBudget betaBudget ε) :
    LowerOrthantApprox μ' (fun ω => prefixVec (eval ω)) γ ε :=
  h.lower_orthant

/-!
## Prefix martingale CLT contract

The serious probability theorem will prove lower-orthant approximation from
`DirectionalInfluenceBound` and `DirectionalQVBound`.  For now we expose it as
a certificate, so downstream Track B code can depend on the exact right shape
without pretending that plain coordinate MOO invariance is enough.
-/

/-- Coefficient-level martingale CLT certificate for one finite rough-core
block. -/
structure PrefixMartingaleCLTCertificate
    {Ω' : Type*} [MeasurableSpace Ω'] {N M : ℕ}
    (μ' : Measure Ω')
    (eval : Ω' → Fin M → ℝ)
    (γ : Measure (Fin M → ℝ))
    (c : Fin M → Finset (Fin N) → ℝ)
    (τ κ ε : ℝ) : Prop where
  directional_influence : DirectionalInfluenceBound c τ
  directional_qv : DirectionalQVBound c κ
  lower_orthant :
    LowerOrthantApprox μ' (fun ω => prefixVec (eval ω)) γ ε

/-- Prefix martingale CLT certificates can be relaxed to a larger
lower-orthant approximation error. -/
theorem PrefixMartingaleCLTCertificate.mono_error
    {Ω' : Type*} [MeasurableSpace Ω'] {N M : ℕ}
    {μ' : Measure Ω'} {eval : Ω' → Fin M → ℝ}
    {γ : Measure (Fin M → ℝ)}
    {c : Fin M → Finset (Fin N) → ℝ}
    {τ κ ε ε' : ℝ}
    (h : PrefixMartingaleCLTCertificate μ' eval γ c τ κ ε)
    (hε : ε ≤ ε') :
    PrefixMartingaleCLTCertificate μ' eval γ c τ κ ε' where
  directional_influence := h.directional_influence
  directional_qv := h.directional_qv
  lower_orthant := h.lower_orthant.mono hε

/-- The CLT certificate gives the crossing replacement used by the finite Track
B block theorem. -/
theorem PrefixMartingaleCLTCertificate.crossing
    {Ω' : Type*} [MeasurableSpace Ω'] {N M : ℕ}
    {μ' : Measure Ω'} {eval : Ω' → Fin M → ℝ}
    {γ : Measure (Fin M → ℝ)}
    {c : Fin M → Finset (Fin N) → ℝ}
    {τ κ ε : ℝ}
    (h : PrefixMartingaleCLTCertificate μ' eval γ c τ κ ε)
    (a : ℝ) :
    |((μ' {ω | eval ω ∈ crossingSet a}).toReal) -
      ((γ (lowerOrthant (fun _ : Fin M => a))).toReal)| ≤ ε :=
  crossing_of_lowerOrthantApprox μ' eval γ a ε h.lower_orthant

/-- A Walsh-Stein lower-orthant certificate can feed the existing
`PrefixMartingaleCLTCertificate` wrapper when the legacy directional
influence/QV predicates are also available.  This keeps downstream Track B
plumbing unchanged while the rough-core replacement theorem is upgraded from
generic martingale CLT language to explicit Walsh-Stein coefficient control. -/
theorem WalshSteinLowerOrthantCertificate.toPrefixMartingaleCLT
    {Ω' : Type*} [MeasurableSpace Ω'] {N M : ℕ}
    {μ' : Measure Ω'} {eval : Ω' → Fin M → ℝ}
    {γ : Measure (Fin M → ℝ)}
    {c : Fin M → Finset (Fin N) → ℝ}
    {D : ℕ}
    {delta boundaryConst K2 K3 gammaBudget betaBudget ε τ κ : ℝ}
    (h :
      WalshSteinLowerOrthantCertificate μ' eval γ c D delta
        boundaryConst K2 K3 gammaBudget betaBudget ε)
    (hinf : DirectionalInfluenceBound c τ)
    (hqv : DirectionalQVBound c κ) :
    PrefixMartingaleCLTCertificate μ' eval γ c τ κ ε where
  directional_influence := hinf
  directional_qv := hqv
  lower_orthant := h.lower_orthant

end Problem1144
end Erdos
