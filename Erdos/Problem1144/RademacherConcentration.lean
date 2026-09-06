import Mathlib.Probability.Moments.SubGaussian
import Erdos.Problem1144.Orthogonality

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem1144

/-!
Reusable concentration facts for the fair-coin Rademacher model.

The active Track B small-product tail reduces to a weighted sum of independent
prime signs.  This file connects the project-specific `eps` coordinates to
mathlib's sub-Gaussian Hoeffding API.
-/

/-- A single Rademacher coordinate has mean zero. -/
theorem integral_eps (p : ℕ) :
    ∫ omega, eps omega p ∂mu = 0 := by
  have hmap : mu.map (fun omega : Omega => omega p) = coin := map_eval_mu p
  calc
    ∫ omega, eps omega p ∂mu = ∫ omega, boolSign (omega p) ∂mu := by rfl
    _ = ∫ b, boolSign b ∂(mu.map fun omega : Omega => omega p) := by
      exact (integral_map (μ := mu) (φ := fun omega : Omega => omega p)
        (measurable_pi_apply p).aemeasurable
        ((measurable_of_finite boolSign).aestronglyMeasurable)).symm
    _ = ∫ b, boolSign b ∂coin := by rw [hmap]
    _ = 0 := integral_boolSign

/-- A single Rademacher coordinate is `1`-sub-Gaussian. -/
theorem hasSubgaussianMGF_eps (p : ℕ) :
    HasSubgaussianMGF (fun omega : Omega => eps omega p) (1 : NNReal) mu := by
  have hb : ∀ᵐ omega ∂mu, eps omega p ∈ Set.Icc (-1 : ℝ) 1 :=
    ae_of_all _ fun omega => by
      unfold eps
      by_cases h : omega p <;> simp [h]
  convert
    (hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
      (μ := mu) (X := fun omega : Omega => eps omega p) (a := -1) (b := 1)
      (measurable_eps p).aemeasurable hb (integral_eps p)) using 1
  norm_num

/-- The Rademacher coordinate signs are independent. -/
theorem iIndepFun_eps :
    iIndepFun (fun p (omega : Omega) => eps omega p) mu := by
  simpa [Function.comp_def, eps_eq_boolSign] using
    (iIndepFun_coordinates.comp
      (fun _p => boolSign)
      (fun _p => measurable_of_finite boolSign))

/-- Weighted Rademacher coordinates are sub-Gaussian with variance proxy equal
to the squared weight. -/
theorem hasSubgaussianMGF_weighted_eps (a : ℕ → ℝ) (p : ℕ) :
    HasSubgaussianMGF (fun omega : Omega => -(a p) * eps omega p)
      (⟨(a p) ^ 2, sq_nonneg (a p)⟩ : NNReal) mu := by
  simpa using (hasSubgaussianMGF_eps p).const_mul (-(a p))

@[simp] theorem abs_eps (omega : Omega) (p : ℕ) :
    |eps omega p| = 1 := by
  unfold eps
  by_cases h : omega p <;> simp [h]

/-- A finite weighted Rademacher linear form over coordinate signs. -/
noncomputable def epsLinearForm (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega) : ℝ :=
  ∑ p ∈ s, a p * eps omega p

/-- Flip exactly the coordinates in a finite fresh sign set. -/
def freshSignFlip (s : Finset ℕ) (omega : Omega) : Omega :=
  fun p => if p ∈ s then !omega p else omega p

/-- The finite fresh-sign flip is measurable. -/
theorem measurable_freshSignFlip (s : Finset ℕ) :
    Measurable (freshSignFlip s) := by
  let flipCoord : (p : ℕ) → Bool → Bool := fun p b => if p ∈ s then !b else b
  change Measurable (fun omega : Omega => fun p => flipCoord p (omega p))
  exact measurable_pi_lambda _ fun p =>
    (measurable_of_finite (flipCoord p)).comp (measurable_pi_apply p)

/-- The one-coordinate Boolean flip preserves the fair coin law. -/
theorem coin_map_not : coin.map (fun b : Bool => !b) = coin := by
  ext t ht
  by_cases hf : false ∈ t <;> by_cases htmem : true ∈ t <;>
    simp [Measure.map_apply (measurable_of_finite fun b : Bool => !b) ht, coin, hf, htmem]

/-- Flipping finitely many fresh signs preserves the infinite product coin
law. -/
theorem measurePreserving_freshSignFlip (s : Finset ℕ) :
    MeasurePreserving (freshSignFlip s) mu mu := by
  let flipCoord : (p : ℕ) → Bool → Bool := fun p b => if p ∈ s then !b else b
  refine ⟨measurable_freshSignFlip s, ?_⟩
  change Measure.map (fun omega : Omega => fun p => flipCoord p (omega p))
      (Measure.infinitePi fun _ : ℕ => coin) = Measure.infinitePi fun _ : ℕ => coin
  rw [Measure.infinitePi_map_pi (fun _ : ℕ => coin)
    (fun p => measurable_of_finite (flipCoord p))]
  congr 1
  funext p
  dsimp [flipCoord]
  by_cases hp : p ∈ s
  · simp [hp, coin_map_not]
  · simp [hp]

@[simp] theorem eps_freshSignFlip_of_mem
    (s : Finset ℕ) (omega : Omega) {p : ℕ} (hp : p ∈ s) :
    eps (freshSignFlip s omega) p = -eps omega p := by
  unfold freshSignFlip eps
  simp [hp]
  cases omega p <;> simp

@[simp] theorem eps_freshSignFlip_of_notMem
    (s : Finset ℕ) (omega : Omega) {p : ℕ} (hp : p ∉ s) :
    eps (freshSignFlip s omega) p = eps omega p := by
  simp [freshSignFlip, eps, hp]

/-- Flipping all coordinates in the support of a finite weighted Rademacher
linear form negates the linear form. -/
theorem epsLinearForm_freshSignFlip
    (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega) :
    epsLinearForm s a (freshSignFlip s omega) = -epsLinearForm s a omega := by
  unfold epsLinearForm
  calc
    ∑ p ∈ s, a p * eps (freshSignFlip s omega) p =
        ∑ p ∈ s, -(a p * eps omega p) := by
      refine Finset.sum_congr rfl ?_
      intro p hp
      rw [eps_freshSignFlip_of_mem s omega hp]
      ring
    _ = -∑ p ∈ s, a p * eps omega p := by
      rw [Finset.sum_neg_distrib]

/-- Finite weighted Rademacher linear forms are measurable. -/
theorem measurable_epsLinearForm (s : Finset ℕ) (a : ℕ → ℝ) :
    Measurable fun omega : Omega => epsLinearForm s a omega := by
  unfold epsLinearForm
  exact Finset.measurable_sum _ fun p _ => (measurable_eps p).const_mul (a p)

/-- The elementary deterministic envelope for a finite weighted Rademacher
linear form. -/
theorem abs_epsLinearForm_le (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega) :
    |epsLinearForm s a omega| ≤ ∑ p ∈ s, |a p| := by
  unfold epsLinearForm
  calc
    |∑ p ∈ s, a p * eps omega p|
        ≤ ∑ p ∈ s, |a p * eps omega p| :=
          Finset.abs_sum_le_sum_abs _ _
    _ = ∑ p ∈ s, |a p| := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          simp [abs_mul]

/-- Every fixed power of a finite weighted Rademacher linear form is
integrable.  This is the boilerplate integrability input needed by the
endpoint-separation second/fourth-moment wrapper. -/
theorem integrable_epsLinearForm_pow
    (s : Finset ℕ) (a : ℕ → ℝ) (k : ℕ) :
    Integrable (fun omega : Omega => (epsLinearForm s a omega) ^ k) mu := by
  let C : ℝ := ∑ p ∈ s, |a p|
  have hmeas :
      AEStronglyMeasurable
        (fun omega : Omega => (epsLinearForm s a omega) ^ k) mu :=
    ((measurable_epsLinearForm s a).pow_const k).aestronglyMeasurable
  refine Integrable.of_bound hmeas (C ^ k) ?_
  exact ae_of_all _ fun omega => by
    have hC : 0 ≤ C := by
      exact Finset.sum_nonneg fun p _hp => abs_nonneg (a p)
    have hbound : |epsLinearForm s a omega| ^ k ≤ C ^ k :=
      pow_le_pow_left₀ (abs_nonneg _) (abs_epsLinearForm_le s a omega) k
    simpa [Real.norm_eq_abs, abs_pow, C] using hbound

/-- Square integrability of a finite weighted Rademacher linear form. -/
theorem integrable_epsLinearForm_sq (s : Finset ℕ) (a : ℕ → ℝ) :
    Integrable (fun omega : Omega => (epsLinearForm s a omega) ^ 2) mu :=
  integrable_epsLinearForm_pow s a 2

/-- Fourth-power integrability of a finite weighted Rademacher linear form. -/
theorem integrable_epsLinearForm_fourth (s : Finset ℕ) (a : ℕ → ℝ) :
    Integrable (fun omega : Omega => (epsLinearForm s a omega) ^ 4) mu :=
  integrable_epsLinearForm_pow s a 4

/-- Product of two coordinate signs is integrable. -/
theorem integrable_eps_mul_eps (p q : ℕ) :
    Integrable (fun omega : Omega => eps omega p * eps omega q) mu := by
  refine
    Integrable.of_bound
      ((measurable_eps p).mul (measurable_eps q)).aestronglyMeasurable
      1 ?_
  exact ae_of_all _ fun omega => by
    simp [Real.norm_eq_abs]

/-- Two-coordinate Rademacher orthogonality. -/
theorem integral_eps_mul_eps (p q : ℕ) :
    ∫ omega, eps omega p * eps omega q ∂mu =
      if p = q then 1 else 0 := by
  by_cases hpq : p = q
  · subst q
    simp [eps_mul_self]
  · let P : Finset ℕ := {p, q}
    let k : ℕ → ℕ := fun r => if r = p then 1 else if r = q then 1 else 0
    have hfun :
        (fun omega : Omega => eps omega p * eps omega q) =
      fun omega : Omega => coordChar P k omega := by
      funext omega
      simp [P, k, coordChar, hpq]
    rw [hfun]
    have hzero :
        ∫ omega, coordChar P k omega ∂mu = 0 := by
      refine integral_coordChar_of_exists_odd P k ?_
      exact ⟨p, by simp [P], by simp [k]⟩
    simpa [hpq] using hzero

/-- The mean of a weighted Rademacher coordinate is zero. -/
theorem integral_weighted_eps (a : ℕ → ℝ) (p : ℕ) :
    ∫ omega, a p * eps omega p ∂mu = 0 := by
  simp [integral_const_mul, integral_eps]

/-- The second moment of a weighted Rademacher coordinate is the square of its
weight. -/
theorem integral_weighted_eps_sq (a : ℕ → ℝ) (p : ℕ) :
    ∫ omega, (a p * eps omega p) ^ 2 ∂mu = a p ^ 2 := by
  calc
    ∫ omega, (a p * eps omega p) ^ 2 ∂mu = ∫ omega, (a p ^ 2 : ℝ) ∂mu := by
      congr 1
      funext omega
      simp [pow_two, mul_comm, mul_left_comm]
    _ = a p ^ 2 := by simp

/-- The third moment of a weighted Rademacher coordinate is zero. -/
theorem integral_weighted_eps_cube (a : ℕ → ℝ) (p : ℕ) :
    ∫ omega, (a p * eps omega p) ^ 3 ∂mu = 0 := by
  calc
    ∫ omega, (a p * eps omega p) ^ 3 ∂mu =
        ∫ omega, (a p ^ 3) * eps omega p ∂mu := by
      congr 1
      funext omega
      simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
    _ = 0 := by simp [integral_const_mul, integral_eps]

/-- The fourth moment of a weighted Rademacher coordinate is the fourth power
of its weight. -/
theorem integral_weighted_eps_fourth (a : ℕ → ℝ) (p : ℕ) :
    ∫ omega, (a p * eps omega p) ^ 4 ∂mu = a p ^ 4 := by
  calc
    ∫ omega, (a p * eps omega p) ^ 4 ∂mu = ∫ omega, (a p ^ 4 : ℝ) ∂mu := by
      congr 1
      funext omega
      simp [pow_succ, mul_comm, mul_left_comm, mul_assoc]
    _ = a p ^ 4 := by simp

/-- Exact variance identity for a finite weighted Rademacher linear form. -/
theorem integral_epsLinearForm_sq_eq_sum_sq
    (s : Finset ℕ) (a : ℕ → ℝ) :
    ∫ omega, (epsLinearForm s a omega) ^ 2 ∂mu =
      ∑ p ∈ s, a p ^ 2 := by
  classical
  unfold epsLinearForm
  rw [show
      (fun omega : Omega => (∑ p ∈ s, a p * eps omega p) ^ 2) =
        fun omega : Omega =>
          (∑ p ∈ s, a p * eps omega p) *
            (∑ p ∈ s, a p * eps omega p) by
        funext omega
        rw [pow_two]]
  simp_rw [Finset.sum_mul_sum]
  rw [integral_finset_sum]
  · refine Finset.sum_congr rfl ?_
    intro p hp
    rw [integral_finset_sum]
    · calc
        ∑ q ∈ s, ∫ omega, (a p * eps omega p) * (a q * eps omega q) ∂mu
            =
          ∑ q ∈ s, if q = p then a p ^ 2 else 0 := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            calc
              ∫ omega, (a p * eps omega p) * (a q * eps omega q) ∂mu
                  =
                a p * a q * ∫ omega, eps omega p * eps omega q ∂mu := by
                  rw [← integral_const_mul]
                  congr 1
                  funext omega
                  ring
              _ = if q = p then a p ^ 2 else 0 := by
                  by_cases hqp : q = p
                  · subst q
                    simp [eps_mul_self, pow_two]
                  · have hpq : p ≠ q := by
                      intro hpq
                      exact hqp hpq.symm
                    simp [integral_eps_mul_eps, hpq, hqp]
        _ = a p ^ 2 := by
            rw [Finset.sum_ite_eq' s p (fun _ => a p ^ 2), if_pos hp]
    · intro q _hq
      have hint :
          Integrable
            (fun omega : Omega => (a p * a q) * (eps omega p * eps omega q)) mu :=
        (integrable_eps_mul_eps p q).const_mul (a p * a q)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hint
  · intro p _hp
    exact
      integrable_finset_sum s fun q _hq => by
        have hint :
            Integrable
              (fun omega : Omega => (a p * a q) * (eps omega p * eps omega q)) mu :=
          (integrable_eps_mul_eps p q).const_mul (a p * a q)
        simpa [mul_comm, mul_left_comm, mul_assoc] using hint

/-- A fresh weighted coordinate is independent of a finite old weighted
Rademacher linear form whose index set does not contain that coordinate. -/
theorem indepFun_weighted_eps_epsLinearForm_of_notMem
    (s : Finset ℕ) (a : ℕ → ℝ) {i : ℕ} (hi : i ∉ s) :
    (fun omega : Omega => a i * eps omega i) ⟂ᵢ[mu]
      (fun omega : Omega => epsLinearForm s a omega) := by
  have hindep : iIndepFun (fun p (omega : Omega) => a p * eps omega p) mu := by
    simpa [Function.comp_def] using
      (iIndepFun_eps.comp
        (fun p x => a p * x)
        (fun p => measurable_const_mul (a p)))
  have hmeas : ∀ p, Measurable (fun omega : Omega => a p * eps omega p) := by
    intro p
    exact (measurable_eps p).const_mul (a p)
  have h := hindep.indepFun_finset_sum_of_notMem hmeas hi
  convert h.symm using 1
  ext omega
  simp [epsLinearForm]

/-- Mixed moments factor for a fresh weighted coordinate and an old finite
weighted Rademacher linear form. -/
theorem integral_weighted_eps_pow_mul_epsLinearForm_pow_of_notMem
    (s : Finset ℕ) (a : ℕ → ℝ) {i : ℕ} (hi : i ∉ s) (m n : ℕ) :
    ∫ omega, (a i * eps omega i) ^ m * (epsLinearForm s a omega) ^ n ∂mu =
      (∫ omega, (a i * eps omega i) ^ m ∂mu) *
        (∫ omega, (epsLinearForm s a omega) ^ n ∂mu) := by
  have hpow :=
    (indepFun_weighted_eps_epsLinearForm_of_notMem s a hi).comp
      (measurable_id.pow_const m) (measurable_id.pow_const n)
  simpa [Function.comp_def] using hpow.integral_fun_mul_eq_mul_integral
    (((measurable_eps i).const_mul (a i)).pow_const m).aestronglyMeasurable
    ((measurable_epsLinearForm s a).pow_const n).aestronglyMeasurable

/-- Powers of a single weighted Rademacher coordinate are integrable. -/
theorem integrable_weighted_eps_pow (a : ℕ → ℝ) (i k : ℕ) :
    Integrable (fun omega : Omega => (a i * eps omega i) ^ k) mu := by
  simpa [epsLinearForm] using (integrable_epsLinearForm_pow ({i} : Finset ℕ) a k)

/-- Mixed products of powers of a fresh coordinate and an old finite linear
form are integrable. -/
theorem integrable_weighted_eps_pow_mul_epsLinearForm_pow_of_notMem
    (s : Finset ℕ) (a : ℕ → ℝ) {i : ℕ} (hi : i ∉ s) (m n : ℕ) :
    Integrable
      (fun omega : Omega => (a i * eps omega i) ^ m * (epsLinearForm s a omega) ^ n)
      mu := by
  have hpow :
      (fun omega : Omega => (a i * eps omega i) ^ m) ⟂ᵢ[mu]
        (fun omega : Omega => (epsLinearForm s a omega) ^ n) :=
    (indepFun_weighted_eps_epsLinearForm_of_notMem s a hi).comp
      (measurable_id.pow_const m) (measurable_id.pow_const n)
  exact hpow.integrable_mul (integrable_weighted_eps_pow a i m)
    (integrable_epsLinearForm_pow s a n)

/-- Exact fourth-moment insertion formula for adding one fresh coordinate to a
finite weighted Rademacher linear form. -/
theorem integral_epsLinearForm_insert_fourth
    (s : Finset ℕ) (a : ℕ → ℝ) {i : ℕ} (hi : i ∉ s) :
    ∫ omega, (epsLinearForm (insert i s) a omega) ^ 4 ∂mu =
      a i ^ 4 + 6 * a i ^ 2 * (∑ p ∈ s, a p ^ 2) +
        ∫ omega, (epsLinearForm s a omega) ^ 4 ∂mu := by
  let X : Omega → ℝ := fun omega => a i * eps omega i
  let L : Omega → ℝ := fun omega => epsLinearForm s a omega
  have hinsert : ∀ omega, epsLinearForm (insert i s) a omega = X omega + L omega := by
    intro omega
    simp [X, L, epsLinearForm, Finset.sum_insert, hi]
  have hexpand :
      (fun omega : Omega => (epsLinearForm (insert i s) a omega) ^ 4) =
        fun omega : Omega =>
          X omega ^ 4 + (4 * (X omega ^ 3 * L omega) +
            (6 * (X omega ^ 2 * L omega ^ 2) +
              (4 * (X omega * L omega ^ 3) + L omega ^ 4))) := by
    funext omega
    rw [hinsert omega]
    ring
  rw [hexpand]
  have hX4 : ∫ omega, X omega ^ 4 ∂mu = a i ^ 4 := by
    simpa [X] using integral_weighted_eps_fourth a i
  have hX3L : ∫ omega, X omega ^ 3 * L omega ∂mu = 0 := by
    have h := integral_weighted_eps_pow_mul_epsLinearForm_pow_of_notMem s a hi 3 1
    simpa [X, L, integral_weighted_eps_cube] using h
  have hX2L2 :
      ∫ omega, X omega ^ 2 * L omega ^ 2 ∂mu =
        a i ^ 2 * (∑ p ∈ s, a p ^ 2) := by
    have h := integral_weighted_eps_pow_mul_epsLinearForm_pow_of_notMem s a hi 2 2
    simpa [X, L, integral_weighted_eps_sq, integral_epsLinearForm_sq_eq_sum_sq] using h
  have hXL3 : ∫ omega, X omega * L omega ^ 3 ∂mu = 0 := by
    have h := integral_weighted_eps_pow_mul_epsLinearForm_pow_of_notMem s a hi 1 3
    simpa [X, L, integral_weighted_eps] using h
  have h_int_X4 : Integrable (fun omega => X omega ^ 4) mu := by
    simpa [X] using integrable_weighted_eps_pow a i 4
  have h_int_X3L : Integrable (fun omega => X omega ^ 3 * L omega) mu := by
    simpa [X, L] using
      integrable_weighted_eps_pow_mul_epsLinearForm_pow_of_notMem s a hi 3 1
  have h_int_X2L2 : Integrable (fun omega => X omega ^ 2 * L omega ^ 2) mu := by
    simpa [X, L] using
      integrable_weighted_eps_pow_mul_epsLinearForm_pow_of_notMem s a hi 2 2
  have h_int_XL3 : Integrable (fun omega => X omega * L omega ^ 3) mu := by
    simpa [X, L] using
      integrable_weighted_eps_pow_mul_epsLinearForm_pow_of_notMem s a hi 1 3
  have h_int_L4 : Integrable (fun omega => L omega ^ 4) mu := by
    simpa [L] using integrable_epsLinearForm_fourth s a
  have h_int_4X3L : Integrable (fun omega => 4 * (X omega ^ 3 * L omega)) mu :=
    h_int_X3L.const_mul 4
  have h_int_6X2L2 : Integrable (fun omega => 6 * (X omega ^ 2 * L omega ^ 2)) mu :=
    h_int_X2L2.const_mul 6
  have h_int_4XL3 : Integrable (fun omega => 4 * (X omega * L omega ^ 3)) mu :=
    h_int_XL3.const_mul 4
  have h_tail1 :
      Integrable
        (fun omega =>
          4 * (X omega ^ 3 * L omega) +
            (6 * (X omega ^ 2 * L omega ^ 2) +
              (4 * (X omega * L omega ^ 3) + L omega ^ 4))) mu :=
    h_int_4X3L.add (h_int_6X2L2.add (h_int_4XL3.add h_int_L4))
  have h_tail2 :
      Integrable
        (fun omega =>
          6 * (X omega ^ 2 * L omega ^ 2) +
            (4 * (X omega * L omega ^ 3) + L omega ^ 4)) mu :=
    h_int_6X2L2.add (h_int_4XL3.add h_int_L4)
  have h_tail3 :
      Integrable (fun omega => 4 * (X omega * L omega ^ 3) + L omega ^ 4) mu :=
    h_int_4XL3.add h_int_L4
  rw [show
      ∫ omega,
          X omega ^ 4 +
            (4 * (X omega ^ 3 * L omega) +
              (6 * (X omega ^ 2 * L omega ^ 2) +
                (4 * (X omega * L omega ^ 3) + L omega ^ 4))) ∂mu =
        ∫ omega, X omega ^ 4 ∂mu +
          ∫ omega,
            4 * (X omega ^ 3 * L omega) +
              (6 * (X omega ^ 2 * L omega ^ 2) +
                (4 * (X omega * L omega ^ 3) + L omega ^ 4)) ∂mu
      from MeasureTheory.integral_add h_int_X4 h_tail1]
  rw [show
      ∫ omega,
          4 * (X omega ^ 3 * L omega) +
            (6 * (X omega ^ 2 * L omega ^ 2) +
              (4 * (X omega * L omega ^ 3) + L omega ^ 4)) ∂mu =
        ∫ omega, 4 * (X omega ^ 3 * L omega) ∂mu +
          ∫ omega,
            6 * (X omega ^ 2 * L omega ^ 2) +
              (4 * (X omega * L omega ^ 3) + L omega ^ 4) ∂mu
      from MeasureTheory.integral_add h_int_4X3L h_tail2]
  rw [show
      ∫ omega,
          6 * (X omega ^ 2 * L omega ^ 2) +
            (4 * (X omega * L omega ^ 3) + L omega ^ 4) ∂mu =
        ∫ omega, 6 * (X omega ^ 2 * L omega ^ 2) ∂mu +
          ∫ omega, 4 * (X omega * L omega ^ 3) + L omega ^ 4 ∂mu
      from MeasureTheory.integral_add h_int_6X2L2 h_tail3]
  rw [show
      ∫ omega, 4 * (X omega * L omega ^ 3) + L omega ^ 4 ∂mu =
        ∫ omega, 4 * (X omega * L omega ^ 3) ∂mu + ∫ omega, L omega ^ 4 ∂mu
      from MeasureTheory.integral_add h_int_4XL3 h_int_L4]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul]
  rw [hX4, hX3L, hX2L2, hXL3]
  ring

/-- Fourth-moment upper bound for finite weighted Rademacher linear forms:
`E Z^4 <= 3 (sum a_p^2)^2`. -/
theorem integral_epsLinearForm_fourth_le_three_sum_sq_sq
    (s : Finset ℕ) (a : ℕ → ℝ) :
    ∫ omega, (epsLinearForm s a omega) ^ 4 ∂mu ≤
      3 * (∑ p ∈ s, a p ^ 2) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp [epsLinearForm]
  | insert i s hi ih =>
      have hinsert := integral_epsLinearForm_insert_fourth s a hi
      have hsum : (∑ p ∈ insert i s, a p ^ 2) = a i ^ 2 + ∑ p ∈ s, a p ^ 2 := by
        simp [Finset.sum_insert, hi]
      rw [hinsert, hsum]
      nlinarith [ih, sq_nonneg (a i ^ 2)]

/-- A positively weighted coordinate sign is sub-Gaussian with variance proxy
equal to the squared weight. -/
theorem hasSubgaussianMGF_pos_weighted_eps (a : ℕ → ℝ) (p : ℕ) :
    HasSubgaussianMGF (fun omega : Omega => a p * eps omega p)
      (⟨(a p) ^ 2, sq_nonneg (a p)⟩ : NNReal) mu := by
  simpa using (hasSubgaussianMGF_eps p).const_mul (a p)

/-- Finite weighted Rademacher linear forms are sub-Gaussian with variance
proxy `sum a_p^2`. -/
theorem hasSubgaussianMGF_epsLinearForm (s : Finset ℕ) (a : ℕ → ℝ) :
    HasSubgaussianMGF (fun omega : Omega => epsLinearForm s a omega)
      (∑ p ∈ s, (⟨(a p) ^ 2, sq_nonneg (a p)⟩ : NNReal)) mu := by
  have hindep :
      iIndepFun (fun p (omega : Omega) => a p * eps omega p) mu := by
    simpa [Function.comp_def] using
      (iIndepFun_eps.comp
        (fun p x => a p * x)
        (fun p => measurable_const_mul (a p)))
  simpa [epsLinearForm] using
    (ProbabilityTheory.HasSubgaussianMGF.sum_of_iIndepFun
      (μ := mu) (X := fun p (omega : Omega) => a p * eps omega p)
      (c := fun p => (⟨(a p) ^ 2, sq_nonneg (a p)⟩ : NNReal))
      hindep
      (s := s)
      (fun p _hp => hasSubgaussianMGF_pos_weighted_eps a p))

/-- Hoeffding upper-tail bound for a finite weighted Rademacher linear form. -/
theorem measure_epsLinearForm_ge_le
    (s : Finset ℕ) (a : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    mu.real {omega | u ≤ epsLinearForm s a omega} ≤
      Real.exp (-u ^ 2 / (2 * (∑ p ∈ s, a p ^ 2))) := by
  have h :=
    ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := mu)
      (X := fun p (omega : Omega) => a p * eps omega p)
      (c := fun p => (⟨(a p) ^ 2, sq_nonneg (a p)⟩ : NNReal))
      (s := s)
      (h_indep := by
        simpa [Function.comp_def] using
          (iIndepFun_eps.comp
            (fun p x => a p * x)
            (fun p => measurable_const_mul (a p))))
      (h_subG := by
        intro p _hp
        exact hasSubgaussianMGF_pos_weighted_eps a p)
      (ε := u) hu
  simpa [epsLinearForm] using h

/-- Hoeffding lower-tail bound for a finite weighted sum of independent
Rademacher coordinates, stated as an upper tail for the negated sum. -/
theorem measure_weighted_eps_neg_sum_ge_le
    (s : Finset ℕ) (a : ℕ → ℝ) {u : ℝ} (hu : 0 ≤ u) :
    mu.real {omega | u ≤ ∑ p ∈ s, (-(a p) * eps omega p)} ≤
      Real.exp (-u ^ 2 / (2 * (∑ p ∈ s, a p ^ 2))) := by
  have h :=
    ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun
      (μ := mu) (X := fun p (omega : Omega) => -(a p) * eps omega p)
      (c := fun p => (⟨(a p) ^ 2, sq_nonneg (a p)⟩ : NNReal))
      (s := s)
      (h_indep := by
        simpa [Function.comp_def] using
          (iIndepFun_eps.comp
            (fun p x => -(a p) * x)
            (fun p => measurable_const_mul (-(a p)))))
      (h_subG := by
        intro p _hp
        exact hasSubgaussianMGF_weighted_eps a p)
      (ε := u) hu
  simpa using h

/-- Convert an exponential log-decay bound to a reciprocal natural-power
budget. -/
theorem real_exp_neg_mul_log_le_inv_pow_nat {b A : ℝ} (n : ℕ)
    (hb : 1 ≤ b) (hA : (n : ℝ) ≤ A) :
    Real.exp (-(A * Real.log b)) ≤ (b ^ n)⁻¹ := by
  have hbpos : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hlog_nonneg : 0 ≤ Real.log b := Real.log_nonneg hb
  have hexp_le :
      Real.exp (-(A * Real.log b)) ≤ Real.exp (-((n : ℝ) * Real.log b)) := by
    rw [Real.exp_le_exp]
    nlinarith
  have hpow : (b ^ n : ℝ) = Real.exp (Real.log b * (n : ℝ)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos hbpos]
  have hrhs : (b ^ n)⁻¹ = Real.exp (-((n : ℝ) * Real.log b)) := by
    rw [hpow, ← Real.exp_neg]
    congr 1
    ring
  simpa [hrhs] using hexp_le

/-- The small-product Hoeffding exponent `81/5` is stronger than the Packet C
`base^-14` budget for every `base >= 1`. -/
theorem real_exp_neg_smallProductExponent_log_le_inv_pow_fourteen {b : ℝ}
    (hb : 1 ≤ b) :
    Real.exp (-(((81 : ℝ) / 5) * Real.log b)) ≤ (b ^ 14)⁻¹ :=
  real_exp_neg_mul_log_le_inv_pow_nat 14 hb (by norm_num)

/-- Scalar arithmetic for the Packet C small-product tail.  A variance proxy
bounded by `1000 * L`, with threshold `180 * L`, gives the exponent
`(81/5) * L`. -/
theorem smallProductHoeffdingExponent_ge_of_variance_proxy {L variance : ℝ}
    (hL : 0 ≤ L) (hvariance_pos : 0 < variance)
    (hvariance : variance ≤ 1000 * L) :
    ((81 : ℝ) / 5) * L ≤ (((9 : ℝ) / 5) * 100 * L) ^ 2 / (2 * variance) := by
  have hden_pos : 0 < 2 * variance := by nlinarith
  have hcoeff_nonneg : 0 ≤ ((81 : ℝ) / 5) * L := by positivity
  have hden_bound : 2 * variance ≤ 2000 * L := by nlinarith
  have hmul :
      ((81 : ℝ) / 5) * L * (2 * variance) ≤ (((9 : ℝ) / 5) * 100 * L) ^ 2 := by
    calc
      ((81 : ℝ) / 5) * L * (2 * variance)
          ≤ ((81 : ℝ) / 5) * L * (2000 * L) :=
            mul_le_mul_of_nonneg_left hden_bound hcoeff_nonneg
      _ = (((9 : ℝ) / 5) * 100 * L) ^ 2 := by ring
  exact (le_div_iff₀ hden_pos).mpr hmul

/-- Logarithmic form of the Packet C small-product exponent check.  This is
the scalar bridge from the deterministic estimate
`sum weights^2 <= 10 * K * log b`, with `K = 100`, to the exponent required by
`measure_event_le_inv_pow_fourteen_of_subset_weighted_eps_neg_sum_ge`. -/
theorem smallProductHoeffdingExponent_log_ge_of_variance_proxy {b variance : ℝ}
    (hb : 1 ≤ b) (hvariance_pos : 0 < variance)
    (hvariance : variance ≤ 10 * 100 * Real.log b) :
    ((81 : ℝ) / 5) * Real.log b ≤
      (((9 : ℝ) / 5) * 100 * Real.log b) ^ 2 / (2 * variance) :=
  smallProductHoeffdingExponent_ge_of_variance_proxy
    (L := Real.log b) (variance := variance) (Real.log_nonneg hb) hvariance_pos
    (by nlinarith)

/-- Scalar part of the small-product log containment: the mean lower bound
`M >= -(11/5) * 100 * L` and the floor bound `log floor <= -4 * 100 * L`
imply the floor is below `M - (9/5) * 100 * L`. -/
theorem smallProduct_log_floor_bound_of_mean_lower {L mean floor : ℝ}
    (hmean : -(((11 : ℝ) / 5) * 100 * L) ≤ mean)
    (hfloor : Real.log floor ≤ -(4 * 100 * L)) :
    Real.log floor ≤ mean - ((9 : ℝ) / 5) * 100 * L := by
  nlinarith

/-- One-prime log identity behind the Packet C small-product tail.  For a
Rademacher sign and `0 < x < 1`, the square of `1 + eps*x` splits into the
deterministic factor `1 - x^2` and the signed log weight
`log ((1+x)/(1-x))`. -/
theorem smallProduct_log_factor_identity_eps
    (omega : Omega) (p : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    2 * Real.log (1 + eps omega p * x) =
      Real.log (1 - x ^ 2) + eps omega p * Real.log ((1 + x) / (1 - x)) := by
  have h1mx : 1 - x ≠ 0 := by nlinarith
  have h1px : 1 + x ≠ 0 := by nlinarith
  have hsq : 1 - x ^ 2 = (1 - x) * (1 + x) := by ring
  unfold eps
  cases h : omega p
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_mul]
    rw [hsq, Real.log_mul h1mx h1px, Real.log_div h1px h1mx]
    ring_nf
  · simp only [↓reduceIte, one_mul]
    rw [hsq, Real.log_mul h1mx h1px, Real.log_div h1px h1mx]
    ring_nf

/-- Each one-prime small-product factor is positive when `0 < x < 1`. -/
theorem smallProduct_factor_pos_eps
    (omega : Omega) (p : ℕ) {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < 1 + eps omega p * x := by
  unfold eps
  cases h : omega p
  · simp only [Bool.false_eq_true, ↓reduceIte, neg_mul]
    nlinarith
  · simp only [↓reduceIte, one_mul]
    nlinarith

/-- The positive log weight `log((1+x)/(1-x))` for `0 < x < 1`. -/
theorem smallProduct_log_weight_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    0 < Real.log ((1 + x) / (1 - x)) := by
  have hden : 0 < 1 - x := by nlinarith
  refine Real.log_pos ?_
  rw [one_lt_div hden]
  nlinarith

/-- A finite small-prime Euler product is positive when all local parameters
lie in `(0,1)`. -/
theorem smallProduct_prod_pos_eps
    (omega : Omega) (s : Finset ℕ) (x : ℕ → ℝ)
    (hx0 : ∀ q ∈ s, 0 < x q) (hx1 : ∀ q ∈ s, x q < 1) :
    0 < ∏ q ∈ s, (1 + eps omega q * x q) := by
  exact Finset.prod_pos fun q hq => smallProduct_factor_pos_eps omega q (hx0 q hq) (hx1 q hq)

/-- The square of a finite small-prime Euler product is positive when all local
parameters lie in `(0,1)`. -/
theorem smallProduct_prod_sq_pos_eps
    (omega : Omega) (s : Finset ℕ) (x : ℕ → ℝ)
    (hx0 : ∀ q ∈ s, 0 < x q) (hx1 : ∀ q ∈ s, x q < 1) :
    0 < (∏ q ∈ s, (1 + eps omega q * x q)) ^ 2 := by
  exact pow_pos (smallProduct_prod_pos_eps omega s x hx0 hx1) 2

/-- A nonempty finite small-prime set has strictly positive log-weight square
sum when all local parameters lie in `(0,1)`. -/
theorem smallProduct_log_weight_sq_sum_pos_of_nonempty
    (s : Finset ℕ) (x : ℕ → ℝ) (hne : s.Nonempty)
    (hx0 : ∀ q ∈ s, 0 < x q) (hx1 : ∀ q ∈ s, x q < 1) :
    0 < ∑ q ∈ s, Real.log ((1 + x q) / (1 - x q)) ^ 2 := by
  rcases hne with ⟨q, hq⟩
  refine Finset.sum_pos' ?_ ⟨q, hq, ?_⟩
  · intro r _hr
    exact sq_nonneg _
  · exact sq_pos_of_ne_zero (ne_of_gt (smallProduct_log_weight_pos (hx0 q hq) (hx1 q hq)))

/-- The intended local small-prime parameter `1 / sqrt(q)` is positive for
positive `q`. -/
theorem smallProduct_inv_sqrt_natCast_pos {q : ℕ} (hq : 0 < q) :
    0 < (Real.sqrt (q : ℝ))⁻¹ := by
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hq))

/-- The intended local small-prime parameter `1 / sqrt(q)` is less than one
for `q >= 2`. -/
theorem smallProduct_inv_sqrt_natCast_lt_one {q : ℕ} (hq : 2 ≤ q) :
    (Real.sqrt (q : ℝ))⁻¹ < 1 := by
  have hqreal : (1 : ℝ) < q := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 1 < 2) hq)
  have hsqrt_gt : 1 < Real.sqrt (q : ℝ) := by
    calc
      (1 : ℝ) = Real.sqrt 1 := by simp
      _ < Real.sqrt (q : ℝ) := Real.sqrt_lt_sqrt zero_le_one hqreal
  exact inv_lt_one_of_one_lt₀ hsqrt_gt

/-- The square of the intended local parameter `1 / sqrt(q)` is the usual
reciprocal `1 / q`. -/
theorem smallProduct_inv_sqrt_natCast_sq_eq_inv_nat {q : ℕ} (hq : 0 < q) :
    ((Real.sqrt (q : ℝ))⁻¹) ^ 2 = ((q : ℝ)⁻¹) := by
  have hnonneg : 0 ≤ (q : ℝ) := by exact_mod_cast hq.le
  rw [inv_pow, Real.sq_sqrt hnonneg]

/-- Rewrite the deterministic mean of the inverse-square-root product into the
standard Mertens product form. -/
theorem smallProduct_inv_sqrt_mean_sum_eq_inv_nat
    (s : Finset ℕ) (hpos : ∀ q, q ∈ s → 0 < q) :
    (∑ q ∈ s, Real.log (1 - ((Real.sqrt (q : ℝ))⁻¹) ^ 2)) =
      ∑ q ∈ s, Real.log (1 - ((q : ℝ)⁻¹)) := by
  refine Finset.sum_congr rfl ?_
  intro q hq
  rw [smallProduct_inv_sqrt_natCast_sq_eq_inv_nat (hpos q hq)]

/-- Elementary bound for the Mertens mean summand on `0 <= x <= 1/2`. -/
theorem smallProduct_neg_log_one_sub_le_add_two_mul_sq {x : ℝ}
    (hx0 : 0 ≤ x) (hx_half : x ≤ (1 : ℝ) / 2) :
    -Real.log (1 - x) ≤ x + 2 * x ^ 2 := by
  have hden_pos : 0 < 1 - x := by linarith
  have hlog_lower : 1 - (1 - x)⁻¹ ≤ Real.log (1 - x) :=
    Real.one_sub_inv_le_log_of_pos hden_pos
  have hlog_upper : -Real.log (1 - x) ≤ (1 - x)⁻¹ - 1 := by
    linarith
  have hfrac_eq : (1 - x)⁻¹ - 1 = x / (1 - x) := by
    field_simp [hden_pos.ne']
    ring
  have hfrac_le : x / (1 - x) ≤ x + 2 * x ^ 2 := by
    rw [div_le_iff₀ hden_pos]
    have hlin_nonneg : 0 ≤ 1 - 2 * x := by linarith
    have hprod_nonneg : 0 ≤ x * x * (1 - 2 * x) :=
      mul_nonneg (mul_nonneg hx0 hx0) hlin_nonneg
    nlinarith
  exact hlog_upper.trans (by simpa [hfrac_eq] using hfrac_le)

/-- Prime-specialized Mertens mean summand bound:
`-log(1 - 1/q) <= 1/q + 2/q^2` for `q >= 2`. -/
theorem smallProduct_neg_log_one_sub_inv_natCast_le {q : ℕ} (hq : 2 ≤ q) :
    -Real.log (1 - ((q : ℝ)⁻¹)) ≤ ((q : ℝ)⁻¹) + 2 * ((q : ℝ)⁻¹) ^ 2 := by
  have hqreal : (2 : ℝ) ≤ q := by exact_mod_cast hq
  have hx0 : 0 ≤ ((q : ℝ)⁻¹) := by positivity
  have hx_half : ((q : ℝ)⁻¹) ≤ (1 : ℝ) / 2 := by
    have hle := one_div_le_one_div_of_le (a := (2 : ℝ)) (b := (q : ℝ))
      (by norm_num) hqreal
    simpa [one_div] using hle
  exact smallProduct_neg_log_one_sub_le_add_two_mul_sq hx0 hx_half

/-- A finite-set version of the Mertens mean bound.  It converts upper bounds
for `sum 1/q` and `sum 1/q^2` into the lower bound on
`sum log (1 - 1/q)` needed by the small-product tail. -/
theorem smallProduct_primeLogMeanLower_of_reciprocal_bounds
    (s : Finset ℕ) (hge_two : ∀ q, q ∈ s → 2 ≤ q) {A B C : ℝ}
    (hrecip : (∑ q ∈ s, ((q : ℝ)⁻¹)) ≤ A)
    (hrecip_sq : (∑ q ∈ s, ((q : ℝ)⁻¹) ^ 2) ≤ B)
    (hC : A + 2 * B ≤ C) :
    -C ≤ ∑ q ∈ s, Real.log (1 - ((q : ℝ)⁻¹)) := by
  have hpoint :
      ∀ q ∈ s,
        -Real.log (1 - ((q : ℝ)⁻¹)) ≤ ((q : ℝ)⁻¹) + 2 * ((q : ℝ)⁻¹) ^ 2 := by
    intro q hq
    exact smallProduct_neg_log_one_sub_inv_natCast_le (hge_two q hq)
  have hsum :
      (∑ q ∈ s, -Real.log (1 - ((q : ℝ)⁻¹))) ≤
        ∑ q ∈ s, (((q : ℝ)⁻¹) + 2 * ((q : ℝ)⁻¹) ^ 2) :=
    Finset.sum_le_sum hpoint
  have hsum_bound :
      (∑ q ∈ s, (((q : ℝ)⁻¹) + 2 * ((q : ℝ)⁻¹) ^ 2)) ≤ C := by
    calc
      (∑ q ∈ s, (((q : ℝ)⁻¹) + 2 * ((q : ℝ)⁻¹) ^ 2))
          = (∑ q ∈ s, ((q : ℝ)⁻¹)) + 2 * ∑ q ∈ s, ((q : ℝ)⁻¹) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ A + 2 * B := by nlinarith
      _ ≤ C := hC
  have hneg_sum :
      -(∑ q ∈ s, Real.log (1 - ((q : ℝ)⁻¹))) ≤ C := by
    rw [← Finset.sum_neg_distrib]
    exact hsum.trans hsum_bound
  linarith

/-- Symmetric logarithm bound: for `r >= 1`,
`log r <= (r - r^-1) / 2`.  The doubled form avoids division in later
rewrites. -/
theorem smallProduct_two_log_le_sub_inv {r : ℝ} (hr : 1 ≤ r) :
    2 * Real.log r ≤ r - r⁻¹ := by
  let f : ℝ → ℝ := fun t => t - t⁻¹ - 2 * Real.log t
  have hmono : MonotoneOn f (Set.Ici (1 : ℝ)) := by
    refine monotoneOn_of_deriv_nonneg (convex_Ici (1 : ℝ)) ?_ ?_ ?_
    · have hcont_id : ContinuousOn (fun t : ℝ => t) (Set.Ici (1 : ℝ)) :=
        continuous_id.continuousOn
      have hcont_inv : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Ici (1 : ℝ)) :=
        hcont_id.inv₀ (by
          intro t ht
          have ht1 : (1 : ℝ) ≤ t := ht
          linarith)
      have hcont_log : ContinuousOn (fun t : ℝ => Real.log t) (Set.Ici (1 : ℝ)) :=
        hcont_id.log (by
          intro t ht
          have ht1 : (1 : ℝ) ≤ t := ht
          linarith)
      exact (hcont_id.sub hcont_inv).sub (hcont_log.const_mul 2)
    · intro x hx
      have hx_gt : 1 < x := by simpa using hx
      have hx_ne : x ≠ 0 := by linarith
      exact (((differentiableAt_id.sub (differentiableAt_inv hx_ne)).sub
        ((Real.differentiableAt_log hx_ne).const_mul 2)).differentiableWithinAt)
    · intro x hx
      have hx_gt : 1 < x := by simpa using hx
      have hx_ne : x ≠ 0 := by linarith
      have hderiv : deriv f x = 1 + (x ^ 2)⁻¹ - 2 * x⁻¹ := by
        have hhas :
            HasDerivAt (fun t : ℝ => t - t⁻¹ - 2 * Real.log t)
              (1 + (x ^ 2)⁻¹ - 2 * x⁻¹) x := by
          convert (((hasDerivAt_id x).sub (hasDerivAt_inv hx_ne)).sub
            ((Real.hasDerivAt_log hx_ne).const_mul 2)) using 1
          all_goals ring_nf
        exact hhas.deriv
      rw [hderiv]
      have hx_pos : 0 < x := by linarith
      have hnonneg : 0 ≤ ((x - 1) ^ 2) / (x ^ 2) := by positivity
      convert hnonneg using 1
      field_simp [hx_ne]
      ring
  have hfr_nonneg : 0 ≤ f r := by
    have hle := hmono (by simp) (by simpa using hr) hr
    simpa [f] using hle
  linarith

/-- Log-ratio upper bound used for the small-product variance weights. -/
theorem smallProduct_log_ratio_le_two_mul_div_one_sub_sq {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) :
    Real.log ((1 + x) / (1 - x)) ≤ 2 * x / (1 - x ^ 2) := by
  have hden_pos : 0 < 1 - x := by linarith
  have hnum_pos : 0 < 1 + x := by linarith
  have hquad_pos : 0 < 1 - x ^ 2 := by
    nlinarith [mul_pos hden_pos hnum_pos]
  have hratio_one : 1 ≤ (1 + x) / (1 - x) := by
    rw [le_div_iff₀ hden_pos]
    nlinarith
  have hlog := smallProduct_two_log_le_sub_inv hratio_one
  have hsub_eq :
      (1 + x) / (1 - x) - (1 - x) / (1 + x) = 4 * x / (1 - x ^ 2) := by
    field_simp [hden_pos.ne', hnum_pos.ne', hquad_pos.ne']
    ring
  have htwolog : 2 * Real.log ((1 + x) / (1 - x)) ≤ 4 * x / (1 - x ^ 2) := by
    simpa [hsub_eq] using hlog
  have hfour_eq : 4 * x / (1 - x ^ 2) = 2 * (2 * x / (1 - x ^ 2)) := by
    ring
  nlinarith

/-- Squared log-ratio bound on the range needed for `x = 1 / sqrt(q)`,
`q >= 2`. -/
theorem smallProduct_log_ratio_sq_le_four_sq_add_twentyfour_fourth {x : ℝ}
    (hx0 : 0 ≤ x) (hx1 : x < 1) (hx_sq_half : x ^ 2 ≤ (1 : ℝ) / 2) :
    Real.log ((1 + x) / (1 - x)) ^ 2 ≤ 4 * x ^ 2 + 24 * x ^ 4 := by
  have hden_pos : 0 < 1 - x := by linarith
  have hratio_one : 1 ≤ (1 + x) / (1 - x) := by
    rw [le_div_iff₀ hden_pos]
    nlinarith
  have hlog_nonneg : 0 ≤ Real.log ((1 + x) / (1 - x)) :=
    Real.log_nonneg hratio_one
  have hlog_le := smallProduct_log_ratio_le_two_mul_div_one_sub_sq hx0 hx1
  have hden_sq_pos : 0 < 1 - x ^ 2 := by nlinarith [sq_nonneg x]
  have hM_nonneg : 0 ≤ 2 * x / (1 - x ^ 2) := by positivity
  have hsq_le :
      Real.log ((1 + x) / (1 - x)) ^ 2 ≤ (2 * x / (1 - x ^ 2)) ^ 2 := by
    rw [sq_le_sq]
    rwa [abs_of_nonneg hlog_nonneg, abs_of_nonneg hM_nonneg]
  have hM_sq_le :
      (2 * x / (1 - x ^ 2)) ^ 2 ≤ 4 * x ^ 2 + 24 * x ^ 4 := by
    rw [div_pow]
    rw [div_le_iff₀ (sq_pos_of_pos hden_sq_pos)]
    nlinarith [sq_nonneg x, sq_nonneg (x ^ 2), sq_nonneg (x ^ 2 - (1 / 2 : ℝ))]
  exact hsq_le.trans hM_sq_le

/-- Prime-specialized variance summand bound for the inverse-square-root
weights. -/
theorem smallProduct_log_weight_sq_inv_sqrt_natCast_le {q : ℕ} (hq : 2 ≤ q) :
    Real.log ((1 + (Real.sqrt (q : ℝ))⁻¹) /
      (1 - (Real.sqrt (q : ℝ))⁻¹)) ^ 2 ≤
      4 * ((q : ℝ)⁻¹) + 24 * ((q : ℝ)⁻¹) ^ 2 := by
  have hq_pos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hx0 : 0 ≤ (Real.sqrt (q : ℝ))⁻¹ := by positivity
  have hx1 : (Real.sqrt (q : ℝ))⁻¹ < 1 :=
    smallProduct_inv_sqrt_natCast_lt_one hq
  have hx2 : ((Real.sqrt (q : ℝ))⁻¹) ^ 2 = ((q : ℝ)⁻¹) :=
    smallProduct_inv_sqrt_natCast_sq_eq_inv_nat hq_pos
  have hx4 : ((Real.sqrt (q : ℝ))⁻¹) ^ 4 = ((q : ℝ)⁻¹) ^ 2 := by
    calc
      ((Real.sqrt (q : ℝ))⁻¹) ^ 4 = (((Real.sqrt (q : ℝ))⁻¹) ^ 2) ^ 2 := by
        ring
      _ = ((q : ℝ)⁻¹) ^ 2 := by rw [hx2]
  have hx_sq_half : ((Real.sqrt (q : ℝ))⁻¹) ^ 2 ≤ (1 : ℝ) / 2 := by
    rw [hx2]
    have hqreal : (2 : ℝ) ≤ q := by exact_mod_cast hq
    have hle := one_div_le_one_div_of_le (a := (2 : ℝ)) (b := (q : ℝ))
      (by norm_num) hqreal
    simpa [one_div] using hle
  have h := smallProduct_log_ratio_sq_le_four_sq_add_twentyfour_fourth hx0 hx1
    hx_sq_half
  simpa [hx2, hx4] using h

/-- Finite-set variance reducer from reciprocal and square-reciprocal bounds. -/
theorem smallProduct_logWeightSqSum_le_of_reciprocal_bounds
    (s : Finset ℕ) (hge_two : ∀ q, q ∈ s → 2 ≤ q) {A B C : ℝ}
    (hrecip : (∑ q ∈ s, ((q : ℝ)⁻¹)) ≤ A)
    (hrecip_sq : (∑ q ∈ s, ((q : ℝ)⁻¹) ^ 2) ≤ B)
    (hC : 4 * A + 24 * B ≤ C) :
    (∑ q ∈ s,
      Real.log ((1 + (Real.sqrt (q : ℝ))⁻¹) /
        (1 - (Real.sqrt (q : ℝ))⁻¹)) ^ 2) ≤ C := by
  have hpoint :
      ∀ q ∈ s,
        Real.log ((1 + (Real.sqrt (q : ℝ))⁻¹) /
          (1 - (Real.sqrt (q : ℝ))⁻¹)) ^ 2 ≤
          4 * ((q : ℝ)⁻¹) + 24 * ((q : ℝ)⁻¹) ^ 2 := by
    intro q hq
    exact smallProduct_log_weight_sq_inv_sqrt_natCast_le (hge_two q hq)
  have hsum :
      (∑ q ∈ s,
        Real.log ((1 + (Real.sqrt (q : ℝ))⁻¹) /
          (1 - (Real.sqrt (q : ℝ))⁻¹)) ^ 2) ≤
        ∑ q ∈ s, (4 * ((q : ℝ)⁻¹) + 24 * ((q : ℝ)⁻¹) ^ 2) :=
    Finset.sum_le_sum hpoint
  have hsum_bound :
      (∑ q ∈ s, (4 * ((q : ℝ)⁻¹) + 24 * ((q : ℝ)⁻¹) ^ 2)) ≤ C := by
    calc
      (∑ q ∈ s, (4 * ((q : ℝ)⁻¹) + 24 * ((q : ℝ)⁻¹) ^ 2))
          = 4 * (∑ q ∈ s, ((q : ℝ)⁻¹)) +
              24 * ∑ q ∈ s, ((q : ℝ)⁻¹) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ 4 * A + 24 * B := by nlinarith
      _ ≤ C := hC
  exact hsum.trans hsum_bound

/-- Finite product version of the Packet C small-product log decomposition.
The deterministic mean is `sum log (1 - x_q^2)`, and the random part is the
weighted Rademacher sum with weights `log ((1+x_q)/(1-x_q))`. -/
theorem smallProduct_log_prod_decomposition_eps
    (omega : Omega) (s : Finset ℕ) (x : ℕ → ℝ)
    (hx0 : ∀ q ∈ s, 0 < x q) (hx1 : ∀ q ∈ s, x q < 1) :
    Real.log ((∏ q ∈ s, (1 + eps omega q * x q)) ^ 2) =
      (∑ q ∈ s, Real.log (1 - x q ^ 2)) +
        ∑ q ∈ s, eps omega q * Real.log ((1 + x q) / (1 - x q)) := by
  have hfactor_ne : ∀ q ∈ s, 1 + eps omega q * x q ≠ 0 := by
    intro q hq
    exact (smallProduct_factor_pos_eps omega q (hx0 q hq) (hx1 q hq)).ne'
  rw [Real.log_pow, Real.log_prod hfactor_ne]
  rw [Finset.mul_sum]
  calc
    (∑ q ∈ s, 2 * Real.log (1 + eps omega q * x q))
        = ∑ q ∈ s, (Real.log (1 - x q ^ 2) +
            eps omega q * Real.log ((1 + x q) / (1 - x q))) := by
          refine Finset.sum_congr rfl ?_
          intro q hq
          exact smallProduct_log_factor_identity_eps omega q (hx0 q hq) (hx1 q hq)
    _ = (∑ q ∈ s, Real.log (1 - x q ^ 2)) +
          ∑ q ∈ s, eps omega q * Real.log ((1 + x q) / (1 - x q)) := by
          rw [Finset.sum_add_distrib]

/-- Convert a pointwise log-product decomposition into the event containment
used by the weighted Rademacher lower-tail bound. -/
theorem smallProduct_bad_subset_weighted_eps_neg_sum_of_log_decomposition
    (X : Omega → ℝ) (floor mean threshold : ℝ) (s : Finset ℕ) (weight : ℕ → ℝ)
    (hX_pos : ∀ omega, 0 < X omega)
    (hlog :
      ∀ omega, Real.log (X omega) = mean + ∑ q ∈ s, eps omega q * weight q)
    (hfloor : Real.log floor ≤ mean - threshold) :
    {omega | X omega < floor} ⊆
      {omega | threshold ≤ ∑ q ∈ s, (-(weight q) * eps omega q)} := by
  intro omega hbad
  let S : ℝ := ∑ q ∈ s, weight q * eps omega q
  have hS_eq : S = ∑ q ∈ s, eps omega q * weight q := by
    dsimp [S]
    refine Finset.sum_congr rfl ?_
    intro q _hq
    ring
  have hmain : mean + S < mean - threshold := by
    calc
      mean + S = mean + ∑ q ∈ s, eps omega q * weight q := by rw [hS_eq]
      _ = Real.log (X omega) := (hlog omega).symm
      _ < Real.log floor := Real.log_lt_log (hX_pos omega) hbad
      _ ≤ mean - threshold := hfloor
  have htail : threshold ≤ -S := by linarith
  have hsum_neg : ∑ q ∈ s, (-(weight q) * eps omega q) = -S := by
    dsimp [S]
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl ?_
    intro q _hq
    ring
  simpa [hsum_neg] using htail

/-- Package the reusable small-product tail pattern: if an event is contained
in a weighted Rademacher lower tail whose Hoeffding exponent is at least
`(81/5) log b`, then the event has the Packet C `b^-14` probability budget. -/
theorem measure_event_le_inv_pow_fourteen_of_subset_weighted_eps_neg_sum_ge
    {bad : Set Omega} (s : Finset ℕ) (a : ℕ → ℝ) {u b : ℝ}
    (hu : 0 ≤ u) (hb : 1 ≤ b)
    (hbad : bad ⊆ {omega | u ≤ ∑ p ∈ s, (-(a p) * eps omega p)})
    (hexp :
      ((81 : ℝ) / 5) * Real.log b ≤ u ^ 2 / (2 * (∑ p ∈ s, a p ^ 2))) :
    mu.real bad ≤ (b ^ 14)⁻¹ := by
  have htail :
      mu.real {omega | u ≤ ∑ p ∈ s, (-(a p) * eps omega p)} ≤
        Real.exp (-u ^ 2 / (2 * (∑ p ∈ s, a p ^ 2))) :=
    measure_weighted_eps_neg_sum_ge_le s a hu
  have hexp_tail :
      Real.exp (-u ^ 2 / (2 * (∑ p ∈ s, a p ^ 2))) ≤
        Real.exp (-(((81 : ℝ) / 5) * Real.log b)) := by
    rw [Real.exp_le_exp]
    simpa [neg_div] using neg_le_neg hexp
  exact (measureReal_mono hbad).trans
    (htail.trans (hexp_tail.trans
      (real_exp_neg_smallProductExponent_log_le_inv_pow_fourteen hb)))

end Problem1144
end Erdos
