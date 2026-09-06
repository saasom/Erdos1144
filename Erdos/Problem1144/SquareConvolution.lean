import Erdos.Problem1144.Orthogonality
import Mathlib.Data.Nat.Sqrt

open scoped BigOperators

namespace Erdos
namespace Problem1144

/-- Squarefree-supported Rademacher function induced by the complete model. -/
noncomputable def gSquarefree (omega : Omega) (n : ℕ) : ℝ := by
  classical
  exact if Squarefree n then f omega n else 0

/-- Divisors `d` such that `d^2` divides `n`. -/
noncomputable def squareDivisors (n : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 n).filter fun d => d ^ 2 ∣ n

/-- Square-kernel smoothing of the squarefree-supported model. -/
noncomputable def squareSmoothing (omega : Omega) (n : ℕ) : ℝ :=
  ∑ d ∈ squareDivisors n, gSquarefree omega (n / d ^ 2)

/-- Summatory function for the squarefree-supported model. -/
noncomputable def GSquarefree (omega : Omega) (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, gSquarefree omega n

/-- On squarefree inputs, the squarefree-supported model agrees with the
complete model. -/
@[simp] theorem gSquarefree_of_squarefree
    (omega : Omega) {n : ℕ} (hn : Squarefree n) :
    gSquarefree omega n = f omega n := by
  simp [gSquarefree, hn]

/-- Non-squarefree inputs contribute zero to the squarefree-supported model. -/
@[simp] theorem gSquarefree_of_not_squarefree
    (omega : Omega) {n : ℕ} (hn : ¬ Squarefree n) :
    gSquarefree omega n = 0 := by
  simp [gSquarefree, hn]

/-- For each integer input, the squarefree-supported model is measurable. -/
theorem measurable_gSquarefree (n : ℕ) :
    Measurable fun omega : Omega => gSquarefree omega n := by
  by_cases hn : Squarefree n
  · simpa [gSquarefree, hn] using measurable_f n
  · simp [gSquarefree, hn]

/-- The square-kernel smoothing is measurable for each integer input. -/
theorem measurable_squareSmoothing (n : ℕ) :
    Measurable fun omega : Omega => squareSmoothing omega n := by
  unfold squareSmoothing
  exact
    Finset.measurable_sum _ fun d _ =>
      measurable_gSquarefree (n / d ^ 2)

/-- The squarefree summatory function is measurable for each cutoff. -/
theorem measurable_GSquarefree (N : ℕ) :
    Measurable fun omega : Omega => GSquarefree omega N := by
  unfold GSquarefree
  exact Finset.measurable_sum _ fun n _ => measurable_gSquarefree n

/-- Membership criterion for square divisors. -/
theorem mem_squareDivisors {d n : ℕ} :
    d ∈ squareDivisors n ↔ 1 ≤ d ∧ d ≤ n ∧ d ^ 2 ∣ n := by
  simp [squareDivisors, and_assoc]

/-- `1` is always a square divisor of a positive integer. -/
theorem one_mem_squareDivisors {n : ℕ} (hn : 0 < n) :
    1 ∈ squareDivisors n := by
  rw [mem_squareDivisors]
  exact ⟨by omega, Nat.succ_le_iff.mp hn, by simp⟩

/-- Square divisors are positive. -/
theorem squareDivisors_pos {d n : ℕ} (hd : d ∈ squareDivisors n) :
    0 < d :=
  lt_of_lt_of_le zero_lt_one (mem_squareDivisors.mp hd).1

/-- A member of `squareDivisors n` has square dividing `n`. -/
theorem squareDivisors_sq_dvd {d n : ℕ} (hd : d ∈ squareDivisors n) :
    d ^ 2 ∣ n :=
  (mem_squareDivisors.mp hd).2.2

/-- A square divisor is bounded by the ambient integer. -/
theorem squareDivisors_le {d n : ℕ} (hd : d ∈ squareDivisors n) :
    d ≤ n :=
  (mem_squareDivisors.mp hd).2.1

/-- Count square multipliers below a fixed quotient.

This is the finite arithmetic count behind the Track B coefficient
`floor_sqrt(n / d)`: for `d > 0`, the positive integers `k` with
`k^2 d <= n` are exactly `1, ..., sqrt(n / d)`.
-/
theorem card_square_multipliers_le (n d : ℕ) (hdpos : 0 < d) :
    ((Finset.Icc 1 n).filter fun k => k ^ 2 * d ≤ n).card =
      Nat.sqrt (n / d) := by
  classical
  have hfin :
      ((Finset.Icc 1 n).filter fun k => k ^ 2 * d ≤ n) =
        Finset.Icc 1 (Nat.sqrt (n / d)) := by
    ext k
    constructor
    · intro hk
      rw [Finset.mem_filter, Finset.mem_Icc] at hk
      have hk_pos : 1 ≤ k := hk.1.1
      have hk2_le_div : k ^ 2 ≤ n / d := by
        rw [Nat.le_div_iff_mul_le hdpos]
        simpa [Nat.mul_comm] using hk.2
      exact Finset.mem_Icc.mpr ⟨hk_pos, (Nat.le_sqrt').mpr hk2_le_div⟩
    · intro hk
      rw [Finset.mem_Icc] at hk
      have hk_pos : 1 ≤ k := hk.1
      have hk2_le_div : k ^ 2 ≤ n / d :=
        (Nat.le_sqrt').mp hk.2
      have hmul : k ^ 2 * d ≤ n := by
        rw [Nat.le_div_iff_mul_le hdpos] at hk2_le_div
        simpa [Nat.mul_comm] using hk2_le_div
      have hk_le_n : k ≤ n := by
        have hd_one : 1 ≤ d := Nat.succ_le_of_lt hdpos
        have hk_le_sq : k ≤ k ^ 2 := by
          simpa [pow_two] using Nat.le_mul_self k
        have hsq_le_prod : k ^ 2 ≤ k ^ 2 * d :=
          Nat.le_mul_of_pos_right (k ^ 2) hdpos
        exact le_trans hk_le_sq (le_trans hsq_le_prod hmul)
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hk_pos, hk_le_n⟩, hmul⟩
  rw [hfin]
  simp

/-- A squarefree summatory cutoff `n / k^2` may be viewed inside the common
ambient range `1, ..., n`, with the square multiplier condition as a filter. -/
theorem GSquarefree_div_sq_eq_squareMultiplierFilter
    (omega : Omega) (n k : ℕ) (hkpos : 0 < k) :
    GSquarefree omega (n / k ^ 2) =
      ∑ d ∈ (Finset.Icc 1 n).filter (fun d => k ^ 2 * d ≤ n),
        gSquarefree omega d := by
  classical
  unfold GSquarefree
  have hk2pos : 0 < k ^ 2 := Nat.pow_pos (n := 2) hkpos
  have hfin :
      Finset.Icc 1 (n / k ^ 2) =
        (Finset.Icc 1 n).filter (fun d => k ^ 2 * d ≤ n) := by
    ext d
    constructor
    · intro hd
      rw [Finset.mem_Icc] at hd
      have hmul : k ^ 2 * d ≤ n := by
        rw [Nat.le_div_iff_mul_le hk2pos] at hd
        simpa [Nat.mul_comm] using hd.2
      have hd_le_n : d ≤ n := by
        exact le_trans hd.2 (Nat.div_le_self n (k ^ 2))
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hd.1, hd_le_n⟩, hmul⟩
    · intro hd
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      have hle_div : d ≤ n / k ^ 2 := by
        rw [Nat.le_div_iff_mul_le hk2pos]
        simpa [Nat.mul_comm] using hd.2
      exact Finset.mem_Icc.mpr ⟨hd.1.1, hle_div⟩
  rw [hfin]

/-- Fubini form of the summatory square-kernel smoothing identity: summing
`GSquarefree (n / k^2)` over square multipliers is the same as summing over
squarefree kernels and then over their admissible square multipliers. -/
theorem sum_GSquarefree_div_sq_eq_squareMultiplierCount
    (omega : Omega) (n : ℕ) :
    (∑ k ∈ Finset.Icc 1 n, GSquarefree omega (n / k ^ 2)) =
      ∑ d ∈ Finset.Icc 1 n,
        ∑ _k ∈ (Finset.Icc 1 n).filter (fun k => k ^ 2 * d ≤ n),
          gSquarefree omega d := by
  classical
  calc
    (∑ k ∈ Finset.Icc 1 n, GSquarefree omega (n / k ^ 2))
        =
      ∑ k ∈ Finset.Icc 1 n,
        ∑ d ∈ (Finset.Icc 1 n).filter (fun d => k ^ 2 * d ≤ n),
          gSquarefree omega d := by
        refine Finset.sum_congr rfl ?_
        intro k hk
        exact
          GSquarefree_div_sq_eq_squareMultiplierFilter omega n k
            ((Finset.mem_Icc.mp hk).1)
    _ =
      ∑ k ∈ Finset.Icc 1 n,
        ∑ d ∈ Finset.Icc 1 n,
          if k ^ 2 * d ≤ n then gSquarefree omega d else 0 := by
        refine Finset.sum_congr rfl ?_
        intro k _hk
        rw [Finset.sum_filter]
    _ =
      ∑ d ∈ Finset.Icc 1 n,
        ∑ k ∈ Finset.Icc 1 n,
          if k ^ 2 * d ≤ n then gSquarefree omega d else 0 := by
        exact Finset.sum_comm
    _ =
      ∑ d ∈ Finset.Icc 1 n,
        ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k ^ 2 * d ≤ n),
          gSquarefree omega d := by
        refine Finset.sum_congr rfl ?_
        intro d _hd
        rw [Finset.sum_filter]

/-! The pointwise square-kernel identity follows from prime-factorization
parity and uniqueness of the squarefree kernel. -/
/-- Adding a square factor does not change the squarefree kernel. -/
theorem sfKernel_eq_of_sq_mul_squarefree
    {n d u : ℕ} (hu : u ≠ 0) (hd : Squarefree d)
    (h : u ^ 2 * d = n) :
    sfKernel n = sfKernel d := by
  ext p
  have hd_ne : d ≠ 0 := hd.ne_zero
  have hfac :
      n.factorization p =
        2 * u.factorization p + d.factorization p := by
    rw [← h]
    have hmul :=
      congrArg (fun q : ℕ →₀ ℕ => q p)
        (Nat.factorization_mul (pow_ne_zero 2 hu) hd_ne)
    simpa [Nat.factorization_pow, Finsupp.add_apply, Finsupp.smul_apply,
      two_mul] using hmul
  rw [mem_sfKernel_iff_odd_factorization,
    mem_sfKernel_iff_odd_factorization, hfac]
  have heven : Even (2 * u.factorization p) :=
    ⟨u.factorization p, by ring⟩
  constructor
  · intro hodd
    exact (Nat.odd_add'.mp hodd).mpr heven
  · intro hodd
    exact Even.add_odd heven hodd

/-- On a squarefree integer, the squarefree kernel records exactly the prime
divisors. -/
theorem mem_sfKernel_iff_dvd_of_squarefree
    {d p : ℕ} (hd : Squarefree d) (hp : Nat.Prime p) :
    p ∈ sfKernel d ↔ p ∣ d := by
  rw [mem_sfKernel_iff_odd_factorization]
  constructor
  · intro hodd
    by_contra hnot
    have hzero : d.factorization p = 0 :=
      Nat.factorization_eq_zero_of_not_dvd hnot
    rw [hzero] at hodd
    exact Nat.not_odd_zero hodd
  · intro hpd
    have hone : d.factorization p = 1 :=
      Nat.factorization_eq_one_of_squarefree hd hp hpd
    rw [hone]
    norm_num

/-- Squarefree integers with the same squarefree kernel are equal. -/
theorem eq_of_squarefree_of_sfKernel_eq
    {a b : ℕ} (ha : Squarefree a) (hb : Squarefree b)
    (hker : sfKernel a = sfKernel b) :
    a = b := by
  rw [Nat.Squarefree.ext_iff ha hb]
  intro p hp
  rw [← mem_sfKernel_iff_dvd_of_squarefree ha hp,
    ← mem_sfKernel_iff_dvd_of_squarefree hb hp, hker]

/-- If `u^2 * a = n` with `a` squarefree, then `f(n)=f(a)`. -/
theorem f_eq_of_sq_mul_squarefree
    (omega : Omega) {n a u : ℕ} (hu : u ≠ 0)
    (ha : Squarefree a) (h : u ^ 2 * a = n) :
    f omega n = f omega a := by
  rw [f, sfKernel_eq_of_sq_mul_squarefree hu ha h, f]

/-- A square divisor whose quotient is squarefree is the unique square
multiplier in a squarefree-kernel decomposition of `n`. -/
theorem squareDivisor_eq_of_squarefree_quotient
    {n a u d : ℕ} (hu : 0 < u) (ha : Squarefree a)
    (h : u ^ 2 * a = n) (hd : d ∈ squareDivisors n)
    (hq : Squarefree (n / d ^ 2)) :
    d = u := by
  let q : ℕ := n / d ^ 2
  have hdvd : d ^ 2 ∣ n := squareDivisors_sq_dvd hd
  have hdpos : 0 < d := squareDivisors_pos hd
  have hqdef : q = n / d ^ 2 := rfl
  have hd_decomp : d ^ 2 * q = n := by
    simpa [q] using Nat.mul_div_cancel' hdvd
  have hq_eq_a : q = a := by
    have hker_q : sfKernel n = sfKernel q :=
      sfKernel_eq_of_sq_mul_squarefree hdpos.ne' (by simpa [q] using hq)
        hd_decomp
    have hker_a : sfKernel n = sfKernel a :=
      sfKernel_eq_of_sq_mul_squarefree hu.ne' ha h
    exact
      eq_of_squarefree_of_sfKernel_eq
        (by simpa [q] using hq) ha (by rw [← hker_q, hker_a])
  have ha_pos : 0 < a := Nat.pos_of_ne_zero ha.ne_zero
  have hsquares : d ^ 2 = u ^ 2 := by
    apply Nat.mul_right_cancel ha_pos
    calc
      d ^ 2 * a = d ^ 2 * q := by rw [hq_eq_a]
      _ = n := hd_decomp
      _ = u ^ 2 * a := h.symm
  exact Nat.pow_left_injective (by norm_num : 2 ≠ 0) hsquares

theorem f_eq_squareSmoothing
  (omega : Omega) {n : ℕ} (hn : 0 < n) :
  f omega n = squareSmoothing omega n := by
  classical
  rcases Nat.sq_mul_squarefree_of_pos hn with
    ⟨a, u, ha_pos, hu_pos, hdecomp, ha_sf⟩
  have hu_mem : u ∈ squareDivisors n := by
    rw [mem_squareDivisors]
    have hu_le_sq : u ≤ u ^ 2 := by
      simpa [pow_two] using Nat.le_mul_self u
    have hu_sq_le_n : u ^ 2 ≤ n := by
      rw [← hdecomp]
      exact Nat.le_mul_of_pos_right (u ^ 2) ha_pos
    exact
      ⟨Nat.succ_le_of_lt hu_pos, le_trans hu_le_sq hu_sq_le_n,
        ⟨a, hdecomp.symm⟩⟩
  have hquot_u : n / u ^ 2 = a := by
    rw [← hdecomp]
    exact Nat.mul_div_right a (Nat.pow_pos (n := 2) hu_pos)
  symm
  unfold squareSmoothing
  rw [Finset.sum_eq_single u]
  · rw [hquot_u, gSquarefree_of_squarefree omega ha_sf]
    exact
      (f_eq_of_sq_mul_squarefree (omega := omega) (n := n) (a := a) (u := u)
        hu_pos.ne' ha_sf hdecomp).symm
  · intro d hd hdu
    by_cases hq : Squarefree (n / d ^ 2)
    · have hdu_eq : d = u :=
        squareDivisor_eq_of_squarefree_quotient hu_pos ha_sf hdecomp hd hq
      exact (hdu hdu_eq).elim
    · simp [gSquarefree, hq]
  · intro hu_not
    exact (hu_not hu_mem).elim

/-- Raw summatory form of the pointwise square-smoothing identity. -/
theorem S_eq_sum_squareSmoothing
  (omega : Omega) (N : ℕ) :
  S omega N = ∑ n ∈ Finset.Icc 1 N, squareSmoothing omega n := by
  rw [S]
  refine Finset.sum_congr rfl ?_
  intro n hn
  exact f_eq_squareSmoothing omega ((Finset.mem_Icc.mp hn).1)

/-- Reindex a sum over multiples of `k^2` by the corresponding quotient. -/
theorem sum_square_multiples_eq_GSquarefree
    (omega : Omega) (N k : ℕ) (hkpos : 0 < k) :
    (∑ n ∈ Finset.Icc 1 N,
        if k ^ 2 ∣ n then gSquarefree omega (n / k ^ 2) else 0) =
      GSquarefree omega (N / k ^ 2) := by
  classical
  rw [← Finset.sum_filter]
  rw [GSquarefree_div_sq_eq_squareMultiplierFilter omega N k hkpos]
  have hk2pos : 0 < k ^ 2 := Nat.pow_pos (n := 2) hkpos
  exact Finset.sum_bij
    (fun n _hn => n / k ^ 2)
    (fun n hn => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one hn.1.1
      have hle_sq : k ^ 2 ≤ n := Nat.le_of_dvd hn_pos hn.2
      have hquot_pos : 0 < n / k ^ 2 := Nat.div_pos hle_sq hk2pos
      have hmul_eq : k ^ 2 * (n / k ^ 2) = n :=
        Nat.mul_div_cancel' hn.2
      exact
        ⟨⟨Nat.succ_le_of_lt hquot_pos,
            le_trans (Nat.div_le_self n (k ^ 2)) hn.1.2⟩,
          by simpa [hmul_eq] using hn.1.2⟩)
    (fun n₁ hn₁ n₂ hn₂ hEq => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hn₁ hn₂
      have hmul₁ : k ^ 2 * (n₁ / k ^ 2) = n₁ :=
        Nat.mul_div_cancel' hn₁.2
      have hmul₂ : k ^ 2 * (n₂ / k ^ 2) = n₂ :=
        Nat.mul_div_cancel' hn₂.2
      have hmul_div_eq : k ^ 2 * (n₁ / k ^ 2) = k ^ 2 * (n₂ / k ^ 2) :=
        congrArg (fun q => k ^ 2 * q) hEq
      calc
        n₁ = k ^ 2 * (n₁ / k ^ 2) := hmul₁.symm
        _ = k ^ 2 * (n₂ / k ^ 2) := hmul_div_eq
        _ = n₂ := hmul₂)
    (fun d hd => by
      rw [Finset.mem_filter, Finset.mem_Icc] at hd
      refine ⟨k ^ 2 * d, ?_, ?_⟩
      · rw [Finset.mem_filter, Finset.mem_Icc]
        have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd.1.1
        have hprod_pos : 0 < k ^ 2 * d := Nat.mul_pos hk2pos hd_pos
        exact
          ⟨⟨Nat.succ_le_of_lt hprod_pos, hd.2⟩,
            ⟨d, rfl⟩⟩
      · exact Nat.mul_div_right d hk2pos)
    (fun n _hn => rfl)

/-- Finite summatory square-convolution identity obtained by exchanging the
square multiplier sum with the squarefree quotient sum. -/
theorem sum_squareSmoothing_eq_sum_GSquarefree_div_sq
    (omega : Omega) (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N, squareSmoothing omega n) =
      ∑ d ∈ Finset.Icc 1 N, GSquarefree omega (N / d ^ 2) := by
  classical
  calc
    (∑ n ∈ Finset.Icc 1 N, squareSmoothing omega n)
        =
      ∑ n ∈ Finset.Icc 1 N,
        ∑ d ∈ Finset.Icc 1 N,
          if d ^ 2 ∣ n then gSquarefree omega (n / d ^ 2) else 0 := by
        refine Finset.sum_congr rfl ?_
        intro n hn
        unfold squareSmoothing
        have hfilter :
            squareDivisors n =
              (Finset.Icc 1 N).filter (fun d => d ^ 2 ∣ n) := by
          ext d
          rw [mem_squareDivisors, Finset.mem_filter, Finset.mem_Icc]
          constructor
          · intro hd
            exact
              ⟨⟨hd.1, le_trans hd.2.1 (Finset.mem_Icc.mp hn).2⟩,
                hd.2.2⟩
          · intro hd
            have hd_pos : 0 < d := lt_of_lt_of_le zero_lt_one hd.1.1
            have hn_pos : 0 < n := lt_of_lt_of_le zero_lt_one
              (Finset.mem_Icc.mp hn).1
            have hd_sq_le_n : d ^ 2 ≤ n := Nat.le_of_dvd hn_pos hd.2
            have hd_le_sq : d ≤ d ^ 2 := by
              simpa [pow_two] using Nat.le_mul_self d
            exact
              ⟨hd.1.1, le_trans hd_le_sq hd_sq_le_n, hd.2⟩
        rw [hfilter, Finset.sum_filter]
    _ =
      ∑ d ∈ Finset.Icc 1 N,
        ∑ n ∈ Finset.Icc 1 N,
          if d ^ 2 ∣ n then gSquarefree omega (n / d ^ 2) else 0 := by
        exact Finset.sum_comm
    _ =
      ∑ d ∈ Finset.Icc 1 N, GSquarefree omega (N / d ^ 2) := by
        refine Finset.sum_congr rfl ?_
        intro d hd
        exact sum_square_multiples_eq_GSquarefree omega N d
          ((Finset.mem_Icc.mp hd).1)

/-- Summatory square-convolution identity.

This follows from `f_eq_squareSmoothing` by exchanging two finite sums and is
the bridge from complete sums to positive square-kernel averages of squarefree
sums.
-/
theorem S_eq_squareSmoothing
  (omega : Omega) (N : ℕ) :
  S omega N =
    ∑ d ∈ Finset.Icc 1 N, GSquarefree omega (N / d ^ 2) := by
  rw [S_eq_sum_squareSmoothing omega N]
  exact sum_squareSmoothing_eq_sum_GSquarefree_div_sq omega N

end Problem1144
end Erdos
