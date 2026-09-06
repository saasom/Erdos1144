import Erdos.Problem1144.HarperCandidateEnergyTwoHeightRectangle
import Erdos.Problem1144.HarperTwoHeightClosedRectangle

open Finset MeasureTheory ProbabilityTheory Set Filter Topology
open scoped BigOperators ENNReal NNReal

namespace Erdos.Problem1144

set_option maxHeartbeats 800000 in
-- The critical cutoff calculation uses this same elaboration allowance;
-- the shifted version also exceeds the default 200000-heartbeat limit.
/-- Actual shifted rectangle estimate with the existing ballot cutoff,
retention, enlargement and error constants. -/
theorem candidate_rankinScheduledCorridorRectangleMass_le_independent_cutoff
    (y j n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) {a b c d : Real}
    (hn : 4 ≤ n)
    (hab : a ≤ b) (hcd : c ≤ d)
    (habWidth : b - a ≤ 65 * (n : Real))
    (hcdWidth : d - c ≤ 65 * (n : Real))
    (hfrequency :
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hendpoint :
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hcovariance :
      |harperRankinTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) σ hσ t s t s| ≤
        1 / (n : Real) ^ (40 : Nat)) :
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat) *
        (harperRankinTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y j) σ hσ t s).real
            (Set.Ioc a b ×ˢ Set.Ioc c d) ≤
      (candidateRankinTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y j) σ hσ t s).real
          (Set.Ioc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
            Set.Ioc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (d + 4 * (1 / (n : Real) ^ (2 : Nat)))) +
        6 / (n : Real) ^ (4 : Nat) := by
  let N : Real := n
  have hN : 4 ≤ N := by
    dsimp only [N]
    exact_mod_cast hn
  have hNpos : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hN2pos : 0 < N ^ (2 : Nat) := pow_pos hNpos _
  have hN4pos : 0 < N ^ (4 : Nat) := pow_pos hNpos _
  have hN8pos : 0 < N ^ (8 : Nat) := pow_pos hNpos _
  have hN40pos : 0 < N ^ (40 : Nat) := pow_pos hNpos _
  have hN48pos : 0 < N ^ (48 : Nat) := pow_pos hNpos _
  have hratio : N ^ (4 : Nat) / N ^ (6 : Nat) = 1 / N ^ (2 : Nat) := by
    field_simp
  have hdelta : 1 / N ^ (2 : Nat) ≤ 1 / 16 := by
    rw [div_le_div_iff₀ hN2pos (by norm_num : (0 : Real) < 16)]
    nlinarith [sq_nonneg (N - 4)]
  have hpiInv : (2 * Real.pi)⁻¹ ≤ (1 : Real) := by
    apply inv_le_one_of_one_le₀
    linarith [Real.pi_gt_three]
  have hpiInv0 : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hpiFactor : (2 * Real.pi)⁻¹ ^ (2 : Nat) ≤ (1 : Real) := by
    nlinarith [sq_nonneg ((2 * Real.pi)⁻¹ - 1)]
  have hfactorG1 :
      |(b + 1 / N ^ (2 : Nat)) -
          (a - 1 / N ^ (2 : Nat))| ≤ 66 * N := by
    rw [abs_of_nonneg]
    · nlinarith
    · nlinarith [div_nonneg (by norm_num : (0 : Real) ≤ 1) hN2pos.le]
  have hfactorG2 :
      |(d + 1 / N ^ (2 : Nat)) -
          (c - 1 / N ^ (2 : Nat))| ≤ 66 * N := by
    rw [abs_of_nonneg]
    · nlinarith
    · nlinarith [div_nonneg (by norm_num : (0 : Real) ≤ 1) hN2pos.le]
  have hfactorR1 :
      |(b + 1 / N ^ (2 : Nat)) -
          (a - 1 / N ^ (2 : Nat))| ≤ 66 * N := by
    rw [abs_of_nonneg]
    · nlinarith
    · nlinarith [div_nonneg (by norm_num : (0 : Real) ≤ 1) hN2pos.le]
  have hfactorR2 :
      |(d + 1 / N ^ (2 : Nat)) -
          (c - 1 / N ^ (2 : Nat))| ≤ 66 * N := by
    rw [abs_of_nonneg]
    · nlinarith
    · nlinarith [div_nonneg (by norm_num : (0 : Real) ≤ 1) hN2pos.le]
  let covariance : Real :=
    |harperRankinTwoHeightBlockCoordinateCovariance y
      (Problem520.harperScheduledPrimeBlock y j) σ hσ t s t s|
  let EG : Real :=
    (2 * Real.pi)⁻¹ ^ (2 : Nat) *
      |(b + 1 / N ^ (2 : Nat)) -
        (a - 1 / N ^ (2 : Nat))| *
      |(d + 1 / N ^ (2 : Nat)) -
        (c - 1 / N ^ (2 : Nat))| *
      (16 * covariance * (N ^ (6 : Nat)) ^ (4 : Nat))
  have hEG : EG ≤ 1 / N ^ (4 : Nat) := by
    have hcov : covariance ≤ 1 / N ^ (40 : Nat) := by
      simpa only [covariance, N] using hcovariance
    calc
      EG ≤ 1 * (66 * N) * (66 * N) *
          (16 * (1 / N ^ (40 : Nat)) *
            (N ^ (6 : Nat)) ^ (4 : Nat)) := by
        dsimp only [EG]
        gcongr
      _ = 69696 / N ^ (14 : Nat) := by
        field_simp
        ring
      _ ≤ 1 / N ^ (4 : Nat) := by
        have hN14pos : 0 < N ^ (14 : Nat) := pow_pos hNpos _
        have hN10 : (69696 : Real) ≤ N ^ (10 : Nat) := by
          calc
            (69696 : Real) ≤ 4 ^ (10 : Nat) := by norm_num
            _ ≤ N ^ (10 : Nat) := by gcongr
        rw [div_le_div_iff₀ hN14pos hN4pos]
        calc
          (69696 : Real) * N ^ (4 : Nat) ≤
              N ^ (10 : Nat) * N ^ (4 : Nat) := by gcongr
          _ = 1 * N ^ (14 : Nat) := by ring
  have hbasePos : 0 < 1048576 * N ^ (48 : Nat) := by positivity
  have hsqrtPos :
      0 < Real.sqrt (Problem520.harperBlockEndpoint j : Real) :=
    hbasePos.trans_le (by simpa only [N] using hendpoint)
  have hinvEndpoint :
      (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ ≤
        (1048576 * N ^ (48 : Nat))⁻¹ := by
    rw [inv_le_inv₀ hsqrtPos hbasePos]
    simpa only [N] using hendpoint
  have hpow30 : N ^ (30 : Nat) ≤ N ^ (36 : Nat) := by
    calc
      N ^ (30 : Nat) = N ^ (30 : Nat) * 1 := by ring
      _ ≤ N ^ (30 : Nat) * N ^ (6 : Nat) := by
        gcongr
        exact one_le_pow₀ hN1
      _ = N ^ (36 : Nat) := by ring
  have hpoly :
      512 * (N ^ (6 : Nat)) ^ (5 : Nat) +
          128 * (N ^ (6 : Nat)) ^ (6 : Nat) ≤
        640 * N ^ (36 : Nat) := by
    calc
      _ = 512 * N ^ (30 : Nat) + 128 * N ^ (36 : Nat) := by ring
      _ ≤ 512 * N ^ (36 : Nat) + 128 * N ^ (36 : Nat) := by gcongr
      _ = 640 * N ^ (36 : Nat) := by ring
  let ER : Real :=
    (2 * Real.pi)⁻¹ ^ (2 : Nat) *
      |(b + 1 / N ^ (2 : Nat)) - (a - 1 / N ^ (2 : Nat))| *
      |(d + 1 / N ^ (2 : Nat)) - (c - 1 / N ^ (2 : Nat))| *
      (Real.sqrt (Problem520.harperBlockEndpoint j : Real))⁻¹ *
        (512 * (N ^ (6 : Nat)) ^ (5 : Nat) +
          128 * (N ^ (6 : Nat)) ^ (6 : Nat))
  have hER : ER ≤ 1 / N ^ (4 : Nat) := by
    calc
      ER ≤ 1 * (66 * N) * (66 * N) *
          (1048576 * N ^ (48 : Nat))⁻¹ *
          (640 * N ^ (36 : Nat)) := by
        dsimp only [ER]
        gcongr
      _ = (5445 / 2048 : Real) / N ^ (10 : Nat) := by
        field_simp
        ring
      _ ≤ 1 / N ^ (4 : Nat) := by
        have hN10pos : 0 < N ^ (10 : Nat) := pow_pos hNpos _
        rw [div_le_div_iff₀ hN10pos hN4pos]
        have hsmall : (5445 / 2048 : Real) ≤ N ^ (6 : Nat) := by
          calc
            (5445 / 2048 : Real) ≤ 4 ^ (6 : Nat) := by norm_num
            _ ≤ N ^ (6 : Nat) := by gcongr
        calc
          (5445 / 2048 : Real) * N ^ (4 : Nat) ≤
              N ^ (6 : Nat) * N ^ (4 : Nat) :=
            mul_le_mul_of_nonneg_right hsmall hN4pos.le
          _ = 1 * N ^ (10 : Nat) := by ring
  let beta : Real := (1 - 2 / N ^ (4 : Nat)) ^ (2 : Nat)
  have hN4geTwo : (2 : Real) ≤ N ^ (4 : Nat) := by
    calc
      (2 : Real) ≤ 4 := by norm_num
      _ ≤ N := hN
      _ = N * 1 := by ring
      _ ≤ N * N ^ (3 : Nat) := by
        gcongr
        exact one_le_pow₀ hN1
      _ = N ^ (4 : Nat) := by ring
  have hTwoDiv : 2 / N ^ (4 : Nat) ≤ 1 := by
    rw [div_le_one hN4pos]
    exact hN4geTwo
  have hbeta0 : 0 ≤ beta := by dsimp only [beta]; positivity
  have hbeta1 : beta ≤ 1 := by
    dsimp only [beta]
    apply pow_le_one₀
    · exact sub_nonneg.mpr hTwoDiv
    · exact sub_le_self 1 (by positivity)
  have hlocal := candidate_rankinScheduledRectangleMass_le_independent_explicit
    y j σ hσ t s (N ^ 6) (N ^ 4) hab hcd (pow_pos hNpos _) hN4geTwo
      (by simpa only [N] using hfrequency)
  rw [hratio] at hlocal
  let P := harperRankinTwoHeightPrimeBlockVectorLaw y
    (Problem520.harperScheduledPrimeBlock y j) σ hσ t s
  let Q := candidateRankinTwoHeightIndependentGaussianBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) σ hσ t s
  have hstart : beta ^ 2 * P.real (Set.Ioc a b ×ˢ Set.Ioc c d) ≤
      beta * P.real (Set.Ioc a b ×ˢ Set.Ioc c d) := by
    apply mul_le_mul_of_nonneg_right _ measureReal_nonneg
    nlinarith
  have hcompare : beta * P.real (Set.Ioc a b ×ˢ Set.Ioc c d) ≤
      Q.real (Set.Ioc (a - 2 * (1 / N ^ 2)) (b + 2 * (1 / N ^ 2)) ×ˢ
        Set.Ioc (c - 2 * (1 / N ^ 2)) (d + 2 * (1 / N ^ 2))) +
        2 / N ^ 4 + EG + ER := by
    convert hlocal using 1 <;> dsimp only [P, Q, beta, EG, ER, covariance] <;> ring
  have hmono : Q.real (Set.Ioc (a - 2 * (1 / N ^ 2)) (b + 2 * (1 / N ^ 2)) ×ˢ
        Set.Ioc (c - 2 * (1 / N ^ 2)) (d + 2 * (1 / N ^ 2))) ≤
      Q.real (Set.Ioc (a - 4 * (1 / N ^ 2)) (b + 4 * (1 / N ^ 2)) ×ˢ
        Set.Ioc (c - 4 * (1 / N ^ 2)) (d + 4 * (1 / N ^ 2))) := by
    apply measureReal_mono _ (measure_ne_top Q _)
    intro z hz
    have hnonneg : 0 ≤ 1 / N ^ 2 := by positivity
    constructor <;> constructor <;> linarith [hz.1.1, hz.1.2, hz.2.1, hz.2.2]
  change beta ^ 2 * P.real (Set.Ioc a b ×ˢ Set.Ioc c d) ≤
    Q.real (Set.Ioc (a - 4 * (1 / N ^ 2)) (b + 4 * (1 / N ^ 2)) ×ˢ
      Set.Ioc (c - 4 * (1 / N ^ 2)) (d + 4 * (1 / N ^ 2))) + 6 / N ^ 4
  apply hstart.trans (hcompare.trans _)
  calc
    _ ≤ Q.real (Set.Ioc (a - 4 * (1 / N ^ 2)) (b + 4 * (1 / N ^ 2)) ×ˢ
        Set.Ioc (c - 4 * (1 / N ^ 2)) (d + 4 * (1 / N ^ 2))) +
        2 / N ^ 4 + 1 / N ^ 4 + 1 / N ^ 4 :=
      add_le_add (add_le_add (add_le_add hmono le_rfl) hEG) hER
    _ = Q.real (Set.Ioc (a - 4 * (1 / N ^ 2)) (b + 4 * (1 / N ^ 2)) ×ˢ
        Set.Ioc (c - 4 * (1 / N ^ 2)) (d + 4 * (1 / N ^ 2))) + 4 / N ^ 4 := by ring
    _ ≤ _ := by gcongr <;> norm_num


/-- Closed-rectangle comparison retains every atom of the actual shifted law. -/
theorem candidate_rankinScheduledClosedRectangleMass_le_independent_cutoff
    (y j n : Nat) (σ : ℝ) (hσ : 0 ≤ σ) (t s : Real) {a b c d : Real}
    (hn : 4 ≤ n)
    (hab : a ≤ b) (hcd : c ≤ d)
    (habWidth : b - a ≤ 65 * (n : Real) - 1)
    (hcdWidth : d - c ≤ 65 * (n : Real) - 1)
    (hfrequency :
      4 * (n : Real) ^ (6 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hendpoint :
      1048576 * (n : Real) ^ (48 : Nat) ≤
        Real.sqrt (Problem520.harperBlockEndpoint j : Real))
    (hcovariance :
      |harperRankinTwoHeightBlockCoordinateCovariance y
          (Problem520.harperScheduledPrimeBlock y j) σ hσ t s t s| ≤
        1 / (n : Real) ^ (40 : Nat)) :
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat) *
        (harperRankinTwoHeightPrimeBlockVectorLaw y
          (Problem520.harperScheduledPrimeBlock y j) σ hσ t s).real
            (Set.Icc a b ×ˢ Set.Icc c d) ≤
      (candidateRankinTwoHeightIndependentGaussianBlockLaw y
        (Problem520.harperScheduledPrimeBlock y j) σ hσ t s).real
          (Set.Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
            Set.Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
              (d + 4 * (1 / (n : Real) ^ (2 : Nat)))) +
        6 / (n : Real) ^ (4 : Nat) := by
  let P := harperRankinTwoHeightPrimeBlockVectorLaw y
    (Problem520.harperScheduledPrimeBlock y j) σ hσ t s
  let Q := candidateRankinTwoHeightIndependentGaussianBlockLaw y
    (Problem520.harperScheduledPrimeBlock y j) σ hσ t s
  let beta : Real :=
    ((1 - 2 / (n : Real) ^ (4 : Nat)) ^ (2 : Nat)) ^ (2 : Nat)
  let err : Real := 6 / (n : Real) ^ (4 : Nat)
  let e : Nat → Real := fun m ↦ (((m + 1 : Nat) : Real))⁻¹
  let A : Nat → Set (Real × Real) := fun m ↦
    Set.Ioc (a - e m) b ×ˢ Set.Ioc (c - e m) d
  let G : Nat → Set (Real × Real) := fun m ↦
    Set.Ioc ((a - e m) - 4 * (1 / (n : Real) ^ (2 : Nat)))
        (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
      Set.Ioc ((c - e m) - 4 * (1 / (n : Real) ^ (2 : Nat)))
        (d + 4 * (1 / (n : Real) ^ (2 : Nat)))
  have hePos (m : Nat) : 0 < e m := by
    dsimp only [e]
    positivity
  have heOne (m : Nat) : e m ≤ 1 := by
    dsimp only [e]
    apply inv_le_one_of_one_le₀
    exact_mod_cast (show 1 ≤ m + 1 by omega)
  have hAanti : Antitone A := by
    intro m k hmk x hx
    have hmkCast : ((m + 1 : Nat) : Real) ≤ (k + 1 : Nat) := by
      exact_mod_cast (show m + 1 ≤ k + 1 by omega)
    have he : e k ≤ e m := by
      dsimp only [e]
      exact inv_anti₀ (by positivity) hmkCast
    rcases hx with ⟨⟨hxa, hxb⟩, hxc, hxd⟩
    exact ⟨⟨by dsimp only [e] at he ⊢; linarith, hxb⟩,
      by dsimp only [e] at he ⊢; linarith, hxd⟩
  have hGanti : Antitone G := by
    intro m k hmk x hx
    have hmkCast : ((m + 1 : Nat) : Real) ≤ (k + 1 : Nat) := by
      exact_mod_cast (show m + 1 ≤ k + 1 by omega)
    have he : e k ≤ e m := by
      dsimp only [e]
      exact inv_anti₀ (by positivity) hmkCast
    rcases hx with ⟨⟨hxa, hxb⟩, hxc, hxd⟩
    exact ⟨⟨by dsimp only [e] at he ⊢; linarith, hxb⟩,
      by dsimp only [e] at he ⊢; linarith, hxd⟩
  have hAmeas (m : Nat) : MeasurableSet (A m) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hGmeas (m : Nat) : MeasurableSet (G m) :=
    measurableSet_Ioc.prod measurableSet_Ioc
  have hAinter : (⋂ m, A m) = Set.Icc a b ×ˢ Set.Icc c d := by
    simpa only [A, e] using
      iInter_prod_Ioc_sub_inv_succ_eq_prod_Icc a b c d
  have hGinter : (⋂ m, G m) =
      Set.Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
          (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
        Set.Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
          (d + 4 * (1 / (n : Real) ^ (2 : Nat))) := by
    have hGeq (m : Nat) : G m =
        Set.Ioc ((a - 4 * (1 / (n : Real) ^ (2 : Nat))) - e m)
            (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
          Set.Ioc ((c - 4 * (1 / (n : Real) ^ (2 : Nat))) - e m)
            (d + 4 * (1 / (n : Real) ^ (2 : Nat))) := by
      dsimp only [G]
      congr 1 <;> ring
    calc
      (⋂ m, G m) =
          ⋂ m,
            Set.Ioc ((a - 4 * (1 / (n : Real) ^ (2 : Nat))) - e m)
                (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
              Set.Ioc ((c - 4 * (1 / (n : Real) ^ (2 : Nat))) - e m)
                (d + 4 * (1 / (n : Real) ^ (2 : Nat))) := by
            congr 1
            funext m
            exact hGeq m
      _ = _ := by
        simpa only [e] using
          iInter_prod_Ioc_sub_inv_succ_eq_prod_Icc
            (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (b + 4 * (1 / (n : Real) ^ (2 : Nat)))
            (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (d + 4 * (1 / (n : Real) ^ (2 : Nat)))
  have hlocal (m : Nat) : beta * P.real (A m) ≤ Q.real (G m) + err := by
    have habm : a - e m ≤ b := by linarith [hab, hePos m]
    have hcdm : c - e m ≤ d := by linarith [hcd, hePos m]
    have hwidthA : b - (a - e m) ≤ 65 * (n : Real) := by
      have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
      nlinarith [habWidth, heOne m]
    have hwidthC : d - (c - e m) ≤ 65 * (n : Real) := by
      have hnR : (4 : Real) ≤ n := by exact_mod_cast hn
      nlinarith [hcdWidth, heOne m]
    simpa only [P, Q, beta, err, A, G, e] using
      candidate_rankinScheduledCorridorRectangleMass_le_independent_cutoff
        y j n σ hσ t s hn habm hcdm hwidthA hwidthC hfrequency hendpoint
          hcovariance
  have hPmeasure : Tendsto (fun m ↦ P (A m)) atTop
      (nhds (P (Set.Icc a b ×ˢ Set.Icc c d))) := by
    simpa only [hAinter] using
      (tendsto_measure_iInter_atTop (μ := P)
        (fun m ↦ (hAmeas m).nullMeasurableSet) hAanti
          ⟨0, measure_ne_top P _⟩)
  have hQmeasure : Tendsto (fun m ↦ Q (G m)) atTop
      (nhds (Q
        (Set.Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
          Set.Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (d + 4 * (1 / (n : Real) ^ (2 : Nat)))))) := by
    simpa only [hGinter] using
      (tendsto_measure_iInter_atTop (μ := Q)
        (fun m ↦ (hGmeas m).nullMeasurableSet) hGanti
          ⟨0, measure_ne_top Q _⟩)
  have hPreal : Tendsto (fun m ↦ P.real (A m)) atTop
      (nhds (P.real (Set.Icc a b ×ˢ Set.Icc c d))) :=
    (ENNReal.tendsto_toReal (measure_ne_top P _)).comp hPmeasure
  have hQreal : Tendsto (fun m ↦ Q.real (G m)) atTop
      (nhds (Q.real
        (Set.Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
          Set.Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
            (d + 4 * (1 / (n : Real) ^ (2 : Nat)))))) :=
    (ENNReal.tendsto_toReal (measure_ne_top Q _)).comp hQmeasure
  change beta * P.real (Set.Icc a b ×ˢ Set.Icc c d) ≤
    Q.real
      (Set.Icc (a - 4 * (1 / (n : Real) ^ (2 : Nat)))
          (b + 4 * (1 / (n : Real) ^ (2 : Nat))) ×ˢ
        Set.Icc (c - 4 * (1 / (n : Real) ^ (2 : Nat)))
          (d + 4 * (1 / (n : Real) ^ (2 : Nat)))) + err
  exact le_of_tendsto_of_tendsto'
    (tendsto_const_nhds.mul hPreal)
    (hQreal.add tendsto_const_nhds)
    hlocal

#print axioms Erdos.Problem1144.iInter_Ioc_sub_inv_succ_eq_Icc
#print axioms Erdos.Problem1144.candidate_rankinScheduledClosedRectangleMass_le_independent_cutoff

end Erdos.Problem1144
