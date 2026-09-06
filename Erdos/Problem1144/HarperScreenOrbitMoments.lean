import Erdos.Problem1144.RademacherConcentration
import Mathlib.Algebra.Order.Chebyshev

open MeasureTheory
open scoped BigOperators ENNReal

namespace Erdos
namespace Problem1144

/-!
# Exact moments on a finite fresh-sign orbit

After the complementary prime world has been frozen, flipping every subset of
a finite fresh set enumerates the full Rademacher cube.  This module proves the
second- and fourth-moment identities directly on that orbit.  The resulting
finite Paley--Zygmund bound does not require a conditional-probability API and
therefore applies verbatim to coefficient vectors selected from the frozen
world.
-/


noncomputable def orbitLinear
    (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega) (t : Finset ℕ) : ℝ :=
  epsLinearForm s a (freshSignFlip t omega)

theorem orbitLinear_insert_of_subset
    {p : ℕ} {s t : Finset ℕ} (hp : p ∉ s) (ht : t ⊆ s)
    (a : ℕ → ℝ) (omega : Omega) :
    orbitLinear (insert p s) a omega t =
      a p * eps omega p + orbitLinear s a omega t := by
  classical
  unfold orbitLinear epsLinearForm
  rw [Finset.sum_insert hp]
  rw [eps_freshSignFlip_of_notMem t omega]
  exact fun hpt => hp (ht hpt)

theorem orbitLinear_insert_flip_of_subset
    {p : ℕ} {s t : Finset ℕ} (hp : p ∉ s) (_ht : t ⊆ s)
    (a : ℕ → ℝ) (omega : Omega) :
    orbitLinear (insert p s) a omega (insert p t) =
      -(a p * eps omega p) + orbitLinear s a omega t := by
  classical
  unfold orbitLinear epsLinearForm
  rw [Finset.sum_insert hp]
  rw [eps_freshSignFlip_of_mem (insert p t) omega (Finset.mem_insert_self p t)]
  rw [show a p * -eps omega p = -(a p * eps omega p) by ring]
  congr 1
  apply Finset.sum_congr rfl
  intro q hqs
  have hqp : q ≠ p := by
    intro h
    subst q
    exact hp hqs
  unfold freshSignFlip eps
  simp [hqp]

theorem sum_orbitLinear_sq
    (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega) :
    (∑ t ∈ s.powerset, orbitLinear s a omega t ^ 2) =
      (2 ^ s.card : ℕ) * ∑ p ∈ s, a p ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [orbitLinear, epsLinearForm]
  | @insert p s hp ih =>
      rw [Finset.sum_powerset_insert hp]
      rw [← Finset.sum_add_distrib]
      have hpair (t : Finset ℕ) (ht : t ∈ s.powerset) :
          orbitLinear (insert p s) a omega t ^ 2 +
              orbitLinear (insert p s) a omega (insert p t) ^ 2 =
            2 * (a p * eps omega p) ^ 2 +
              2 * orbitLinear s a omega t ^ 2 := by
        rw [orbitLinear_insert_of_subset hp (Finset.mem_powerset.mp ht) a omega,
          orbitLinear_insert_flip_of_subset hp (Finset.mem_powerset.mp ht) a omega]
        ring
      rw [Finset.sum_congr rfl hpair]
      have heps : (eps omega p) ^ 2 = 1 := by
        rw [pow_two, eps_mul_self]
      simp_rw [mul_pow, heps, mul_one]
      rw [Finset.card_insert_of_notMem hp, pow_succ, Finset.sum_insert hp]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
      rw [← Finset.mul_sum, ih]
      norm_num [Nat.cast_mul]
      ring

theorem sum_orbitLinear_fourth_le
    (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega) :
    (∑ t ∈ s.powerset, orbitLinear s a omega t ^ 4) ≤
      3 * (2 ^ s.card : ℕ) * (∑ p ∈ s, a p ^ 2) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [orbitLinear, epsLinearForm]
  | @insert p s hp ih =>
      rw [Finset.sum_powerset_insert hp, ← Finset.sum_add_distrib]
      have hpair (t : Finset ℕ) (ht : t ∈ s.powerset) :
          orbitLinear (insert p s) a omega t ^ 4 +
              orbitLinear (insert p s) a omega (insert p t) ^ 4 =
            2 * (a p * eps omega p) ^ 4 +
              12 * (a p * eps omega p) ^ 2 *
                orbitLinear s a omega t ^ 2 +
              2 * orbitLinear s a omega t ^ 4 := by
        rw [orbitLinear_insert_of_subset hp (Finset.mem_powerset.mp ht) a omega,
          orbitLinear_insert_flip_of_subset hp (Finset.mem_powerset.mp ht) a omega]
        ring
      rw [Finset.sum_congr rfl hpair]
      have heps2 : (eps omega p) ^ 2 = 1 := by
        rw [pow_two, eps_mul_self]
      have heps4 : (eps omega p) ^ 4 = 1 := by
        rw [show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, heps2]
        simp
      simp_rw [mul_pow, heps2, heps4, mul_one]
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      simp only [Finset.sum_const, Finset.card_powerset, nsmul_eq_mul]
      rw [← Finset.mul_sum]
      rw [sum_orbitLinear_sq]
      rw [show (∑ x ∈ s.powerset,
          2 * orbitLinear s a omega x ^ 4) =
            2 * (∑ x ∈ s.powerset, orbitLinear s a omega x ^ 4) by
          rw [Finset.mul_sum]]
      rw [Finset.card_insert_of_notMem hp, pow_succ, Finset.sum_insert hp]
      have hC : 0 ≤ ((2 ^ s.card : ℕ) : ℝ) := by positivity
      have hb : 0 ≤ a p ^ 2 := sq_nonneg _
      have hV : 0 ≤ ∑ x ∈ s, a x ^ 2 :=
        Finset.sum_nonneg fun x _hx => sq_nonneg _
      have hmono :
          ((2 ^ s.card : ℕ) : ℝ) * (2 * a p ^ 4) +
                12 * a p ^ 2 *
                  (((2 ^ s.card : ℕ) : ℝ) * ∑ x ∈ s, a x ^ 2) +
                2 * ∑ x ∈ s.powerset, orbitLinear s a omega x ^ 4
              ≤
            ((2 ^ s.card : ℕ) : ℝ) * (2 * a p ^ 4) +
                12 * a p ^ 2 *
                  (((2 ^ s.card : ℕ) : ℝ) * ∑ x ∈ s, a x ^ 2) +
                2 *
                  (3 * ((2 ^ s.card : ℕ) : ℝ) *
                    (∑ x ∈ s, a x ^ 2) ^ 2) := by
        gcongr
      have hfinal :
          ((2 ^ s.card : ℕ) : ℝ) * (2 * a p ^ 4) +
                12 * a p ^ 2 *
                  (((2 ^ s.card : ℕ) : ℝ) * ∑ x ∈ s, a x ^ 2) +
                2 *
                  (3 * ((2 ^ s.card : ℕ) : ℝ) *
                    (∑ x ∈ s, a x ^ 2) ^ 2)
              ≤
            3 * (((2 ^ s.card : ℕ) : ℝ) * 2) *
              (a p ^ 2 + ∑ x ∈ s, a x ^ 2) ^ 2 := by
        nlinarith [mul_nonneg hC (sq_nonneg (a p ^ 2))]
      rw [show (((2 ^ (s.card + 1) : ℕ) : ℝ)) =
          ((2 ^ s.card : ℕ) : ℝ) * 2 by
        norm_num [pow_succ, Nat.cast_mul]]
      convert hmono.trans hfinal using 1

noncomputable def orbitLargeSet
    (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega) (U : ℝ) : Finset (Finset ℕ) := by
  classical
  exact s.powerset.filter fun t => U ≤ |orbitLinear s a omega t|

theorem card_orbitLargeSet_lower
    (s : Finset ℕ) (a : ℕ → ℝ) (omega : Omega) (U : ℝ)
    (hV : 0 < ∑ p ∈ s, a p ^ 2)
    (hU : U ^ 2 ≤ (∑ p ∈ s, a p ^ 2) / 2) :
    ((2 ^ s.card : ℕ) : ℝ) / 12 ≤
      ((orbitLargeSet s a omega U).card : ℝ) := by
  classical
  let P := s.powerset
  let G := orbitLargeSet s a omega U
  let V : ℝ := ∑ p ∈ s, a p ^ 2
  by_cases hUnonpos : U ≤ 0
  · have hG : G = P := by
      apply Finset.filter_eq_self.mpr
      intro t ht
      exact hUnonpos.trans (abs_nonneg _)
    change ((2 ^ s.card : ℕ) : ℝ) / 12 ≤ (G.card : ℝ)
    rw [hG]
    simp only [P, Finset.card_powerset]
    have hC : 0 ≤ (((2 ^ s.card : ℕ) : ℝ)) := by positivity
    linarith
  · have hUpos : 0 < U := lt_of_not_ge hUnonpos
    have hGsub : G ⊆ P := Finset.filter_subset _ _
    have hpoint (t : Finset ℕ) (ht : t ∈ P) :
        orbitLinear s a omega t ^ 2 ≤
          U ^ 2 + if t ∈ G then orbitLinear s a omega t ^ 2 else 0 := by
      by_cases htG : t ∈ G
      · simp [htG, sq_nonneg (U)]
      · have htNotLarge : ¬ U ≤ |orbitLinear s a omega t| := by
          intro hlarge
          exact htG (Finset.mem_filter.mpr ⟨ht, hlarge⟩)
        have habs : |orbitLinear s a omega t| ≤ U :=
          (lt_of_not_ge htNotLarge).le
        have hsq := pow_le_pow_left₀ (abs_nonneg _) habs 2
        rw [← abs_pow, abs_of_nonneg (sq_nonneg _)] at hsq
        simpa [htG] using hsq
    have hsumUpper :
        (∑ t ∈ P, orbitLinear s a omega t ^ 2) ≤
          (P.card : ℝ) * U ^ 2 +
            ∑ t ∈ G, orbitLinear s a omega t ^ 2 := by
      calc
        (∑ t ∈ P, orbitLinear s a omega t ^ 2)
            ≤ ∑ t ∈ P,
                (U ^ 2 + if t ∈ G then orbitLinear s a omega t ^ 2 else 0) :=
              Finset.sum_le_sum hpoint
        _ = (P.card : ℝ) * U ^ 2 +
              ∑ t ∈ P,
                if t ∈ G then orbitLinear s a omega t ^ 2 else 0 := by
              rw [Finset.sum_add_distrib]
              simp [nsmul_eq_mul]
        _ = (P.card : ℝ) * U ^ 2 +
              ∑ t ∈ G, orbitLinear s a omega t ^ 2 := by
              congr 1
              rw [← Finset.sum_filter]
              apply Finset.sum_congr
              · ext t
                simp only [Finset.mem_filter]
                constructor
                · exact fun h => h.2
                · exact fun h => ⟨hGsub h, h⟩
              · intro t _ht
                rfl
    have hsecond :
        (P.card : ℝ) * V =
          ∑ t ∈ P, orbitLinear s a omega t ^ 2 := by
      simpa [P, V, Finset.card_powerset, mul_comm] using
        (sum_orbitLinear_sq s a omega).symm
    have hgoodSecond :
        (P.card : ℝ) * V / 2 ≤
          ∑ t ∈ G, orbitLinear s a omega t ^ 2 := by
      have hPnonneg : 0 ≤ (P.card : ℝ) := by positivity
      have hUscaled : (P.card : ℝ) * U ^ 2 ≤ (P.card : ℝ) * (V / 2) :=
        mul_le_mul_of_nonneg_left (by simpa [V] using hU) hPnonneg
      rw [← hsecond] at hsumUpper
      linarith
    have hcauchy :
        (∑ t ∈ G, orbitLinear s a omega t ^ 2) ^ 2 ≤
          (G.card : ℝ) *
            ∑ t ∈ G, (orbitLinear s a omega t ^ 2) ^ 2 := by
      simpa using
        (sq_sum_le_card_mul_sum_sq (s := G)
          (f := fun t => orbitLinear s a omega t ^ 2))
    have hfourthG :
        (∑ t ∈ G, (orbitLinear s a omega t ^ 2) ^ 2) ≤
          3 * (P.card : ℝ) * V ^ 2 := by
      calc
        (∑ t ∈ G, (orbitLinear s a omega t ^ 2) ^ 2)
            = ∑ t ∈ G, orbitLinear s a omega t ^ 4 := by
                apply Finset.sum_congr rfl
                intro t _ht
                ring
        _ ≤ ∑ t ∈ P, orbitLinear s a omega t ^ 4 := by
              exact Finset.sum_le_sum_of_subset_of_nonneg hGsub
                (fun _t _htP _htG => by positivity)
        _ ≤ 3 * (P.card : ℝ) * V ^ 2 := by
              simpa [P, V, Finset.card_powerset] using
                sum_orbitLinear_fourth_le s a omega
    have hcombined :
        ((P.card : ℝ) * V / 2) ^ 2 ≤
          (G.card : ℝ) * (3 * (P.card : ℝ) * V ^ 2) := by
      calc
        ((P.card : ℝ) * V / 2) ^ 2
            ≤ (∑ t ∈ G, orbitLinear s a omega t ^ 2) ^ 2 :=
              pow_le_pow_left₀ (by positivity) hgoodSecond 2
        _ ≤ (G.card : ℝ) *
              ∑ t ∈ G, (orbitLinear s a omega t ^ 2) ^ 2 := hcauchy
        _ ≤ (G.card : ℝ) * (3 * (P.card : ℝ) * V ^ 2) :=
              mul_le_mul_of_nonneg_left hfourthG (by positivity)
    have hPpos : 0 < (P.card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨∅, by simp [P]⟩
    have hGnonneg : 0 ≤ (G.card : ℝ) := by positivity
    have hVpos : 0 < V := by simpa [V] using hV
    have hDpos : 0 < (P.card : ℝ) * V ^ 2 :=
      mul_pos hPpos (sq_pos_of_pos hVpos)
    have hmul :
        ((P.card : ℝ) / 4) * ((P.card : ℝ) * V ^ 2) ≤
          (3 * (G.card : ℝ)) * ((P.card : ℝ) * V ^ 2) := by
      convert hcombined using 1 <;> ring
    have hcancel : (P.card : ℝ) / 4 ≤ 3 * (G.card : ℝ) := by
      nlinarith
    have htarget : (P.card : ℝ) / 12 ≤ (G.card : ℝ) := by
      linarith
    simpa [P, G, Finset.card_powerset] using htarget

/-!
## From a pointwise orbit count to probability

Every subset flip preserves the ambient coin law.  Consequently a uniform
lower bound for the number of successful worlds in each good orbit integrates
to the same lower bound for the actual probability, provided the good event is
itself invariant on the orbit.
-/

/-- Number of subset flips of `s` that move `omega` into `E`. -/
noncomputable def orbitEventCount
    (s : Finset ℕ) (E : Set Omega) (omega : Omega) : ℝ := by
  classical
  exact ((s.powerset.filter fun t => freshSignFlip t omega ∈ E).card : ℝ)

theorem orbitEventCount_eq_sum_indicator
    (s : Finset ℕ) (E : Set Omega) (omega : Omega) :
    orbitEventCount s E omega =
      ∑ t ∈ s.powerset,
        (freshSignFlip t ⁻¹' E).indicator
          (fun _ : Omega => (1 : ℝ)) omega := by
  classical
  unfold orbitEventCount
  rw [Finset.card_filter]
  simp only [Set.indicator, Set.mem_preimage]
  norm_cast

theorem measurable_orbitEventCount
    (s : Finset ℕ) {E : Set Omega} (hE : MeasurableSet E) :
    Measurable (orbitEventCount s E) := by
  have hfun : orbitEventCount s E = fun omega =>
      ∑ t ∈ s.powerset,
        (freshSignFlip t ⁻¹' E).indicator
          (fun _ : Omega => (1 : ℝ)) omega := by
    funext omega
    exact orbitEventCount_eq_sum_indicator s E omega
  rw [hfun]
  exact Finset.measurable_sum _ fun t _ht =>
    measurable_const.indicator (hE.preimage (measurable_freshSignFlip t))

theorem integrable_orbitEventCount
    (s : Finset ℕ) {E : Set Omega} (hE : MeasurableSet E) :
    Integrable (orbitEventCount s E) mu := by
  classical
  refine Integrable.of_bound
    (measurable_orbitEventCount s hE).aestronglyMeasurable
    (s.powerset.card : ℝ) ?_
  exact ae_of_all mu fun omega => by
    have hnonneg : 0 ≤ orbitEventCount s E omega := by
      unfold orbitEventCount
      positivity
    rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
    unfold orbitEventCount
    exact_mod_cast
      Finset.card_filter_le s.powerset (fun t => freshSignFlip t omega ∈ E)

/-- Exact orbit-count integral. -/
theorem integral_indicator_orbitEventCount
    (s : Finset ℕ) {G E : Set Omega}
    (hG : MeasurableSet G) (hE : MeasurableSet E)
    (hinv : ∀ t, t ∈ s.powerset → ∀ omega,
      omega ∈ G ↔ freshSignFlip t omega ∈ G) :
    (∫ omega, G.indicator (orbitEventCount s E) omega ∂mu) =
      (2 ^ s.card : ℕ) * mu.real (G ∩ E) := by
  classical
  have hfun :
      (fun omega => G.indicator (orbitEventCount s E) omega) =
        fun omega => ∑ t ∈ s.powerset,
          (freshSignFlip t ⁻¹' (G ∩ E)).indicator
            (fun _ : Omega => (1 : ℝ)) omega := by
    funext omega
    by_cases homegaG : omega ∈ G
    · rw [Set.indicator_of_mem homegaG]
      rw [orbitEventCount_eq_sum_indicator]
      apply Finset.sum_congr rfl
      intro t ht
      have hflipG : freshSignFlip t omega ∈ G :=
        (hinv t ht omega).mp homegaG
      by_cases hflipE : freshSignFlip t omega ∈ E
      · simp [hflipG, hflipE]
      · simp [hflipG, hflipE]
    · rw [Set.indicator_of_notMem homegaG]
      symm
      apply Finset.sum_eq_zero
      intro t ht
      have hflipNotG : freshSignFlip t omega ∉ G := by
        intro h
        exact homegaG ((hinv t ht omega).mpr h)
      simp [hflipNotG]
  rw [hfun, integral_finset_sum]
  · calc
      (∑ t ∈ s.powerset,
          ∫ omega,
            (freshSignFlip t ⁻¹' (G ∩ E)).indicator
              (fun _ : Omega => (1 : ℝ)) omega ∂mu) =
          ∑ _t ∈ s.powerset, mu.real (G ∩ E) := by
            apply Finset.sum_congr rfl
            intro t _ht
            calc
              (∫ omega,
                  (freshSignFlip t ⁻¹' (G ∩ E)).indicator
                    (fun _ : Omega => (1 : ℝ)) omega ∂mu) =
                  mu.real (freshSignFlip t ⁻¹' (G ∩ E)) := by
                    simpa using integral_indicator_one
                      (μ := mu)
                      ((hG.inter hE).preimage (measurable_freshSignFlip t))
              _ = mu.real (G ∩ E) :=
                    (measurePreserving_freshSignFlip t).measureReal_preimage
                      (hG.inter hE).nullMeasurableSet
      _ = (2 ^ s.card : ℕ) * mu.real (G ∩ E) := by
            simp [nsmul_eq_mul]
  · intro t _ht
    exact (integrable_const (1 : ℝ)).indicator
      ((hG.inter hE).preimage (measurable_freshSignFlip t))

/-- A pointwise lower density `c` of successes on each invariant good orbit
gives probability at least `c * P(G)` for simultaneous goodness and success. -/
theorem measureReal_inter_lower_of_orbitEventCount
    (s : Finset ℕ) {G E : Set Omega}
    (hG : MeasurableSet G) (hE : MeasurableSet E)
    (hinv : ∀ t, t ∈ s.powerset → ∀ omega,
      omega ∈ G ↔ freshSignFlip t omega ∈ G)
    (c : ℝ)
    (hcount : ∀ omega ∈ G,
      c * (2 ^ s.card : ℕ) ≤ orbitEventCount s E omega) :
    c * mu.real G ≤ mu.real (G ∩ E) := by
  have hCpos : 0 < (((2 ^ s.card : ℕ) : ℝ)) := by positivity
  have hpoint : ∀ omega,
      G.indicator (fun _ : Omega => c * (2 ^ s.card : ℕ)) omega ≤
        G.indicator (orbitEventCount s E) omega := by
    intro omega
    by_cases homega : omega ∈ G
    · rw [Set.indicator_of_mem homega, Set.indicator_of_mem homega]
      exact hcount omega homega
    · simp [homega]
  have hleftInt :
      (∫ omega,
        G.indicator (fun _ : Omega => c * (2 ^ s.card : ℕ)) omega ∂mu) =
        (c * (2 ^ s.card : ℕ)) * mu.real G := by
    rw [integral_indicator_const (c * (2 ^ s.card : ℕ)) hG]
    simp [smul_eq_mul, mul_comm]
  have hrightInt :
      (∫ omega, G.indicator (orbitEventCount s E) omega ∂mu) =
        (2 ^ s.card : ℕ) * mu.real (G ∩ E) :=
    integral_indicator_orbitEventCount s hG hE hinv
  have hmono :
      (∫ omega,
        G.indicator (fun _ : Omega => c * (2 ^ s.card : ℕ)) omega ∂mu) ≤
      ∫ omega, G.indicator (orbitEventCount s E) omega ∂mu := by
    apply integral_mono
    · exact (integrable_const _).indicator hG
    · exact (integrable_orbitEventCount s hE).indicator hG
    · exact hpoint
  rw [hleftInt, hrightInt] at hmono
  nlinarith


end Problem1144
end Erdos

#print axioms Erdos.Problem1144.sum_orbitLinear_sq
#print axioms Erdos.Problem1144.sum_orbitLinear_fourth_le
#print axioms Erdos.Problem1144.card_orbitLargeSet_lower
#print axioms Erdos.Problem1144.measureReal_inter_lower_of_orbitEventCount
