import Erdos.Problem1144.HarperCoefficientScaleEnergy

open MeasureTheory Set

namespace Erdos
namespace Problem1144

/-!
# Rankin-shift localization at the fresh-coefficient boundary

Harper's slight right shift of the Euler product has an exact deterministic
effect on the Parseval energy.  Half of the shift suppresses the tail beyond
the coefficient boundary.  This file proves the resulting localization
inequality without any probabilistic or number-theoretic assumptions.
-/

/-- The squarefree smooth energy with a Rankin shift `a`. -/
noncomputable def harperSquarefreeShiftedSmoothEnergy
    (y : ℕ) (a : ℝ) (omega : Problem520.Omega) : ℝ :=
  ∫ z in Set.Ioi (1 : ℝ),
    (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-a)

theorem rpow_neg_le_one_of_one_le
    {z a : ℝ} (hz : 1 ≤ z) (ha : 0 ≤ a) :
    z ^ (-a) ≤ 1 := by
  exact (Real.rpow_le_one_iff_of_pos (by positivity)).2
    (Or.inl ⟨hz, neg_nonpos.mpr ha⟩)

theorem integrableOn_harperSquarefreeShiftedSmoothEnergy
    (y : ℕ) (omega : Problem520.Omega) {a : ℝ} (ha : 0 ≤ a) :
    IntegrableOn
      (fun z : ℝ ↦
        (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-a))
      (Set.Ioi (1 : ℝ)) := by
  have hbase : Integrable
      (fun z : ℝ ↦ |Problem520.ΨReal omega z y| ^ 2 / z ^ 2)
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    (Problem520.integrableOn_smoothEnergy_integrand omega y).mono_set
      (Set.Ioi_subset_Ioi (by norm_num))
  apply hbase.mono'
  · exact ((((Problem520.measurable_ΨReal_cutoff omega y).abs.pow_const 2).div
      (measurable_id.pow_const 2)).mul
        (measurable_id.pow_const (-a))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hz0 : 0 ≤ z := (show (1 : ℝ) < z from hz).le.trans' (by norm_num)
    have hbase0 : 0 ≤ |Problem520.ΨReal omega z y| ^ 2 / z ^ 2 :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    have hw0 : 0 ≤ z ^ (-a) := Real.rpow_nonneg hz0 _
    rw [Real.norm_of_nonneg (mul_nonneg hbase0 hw0)]
    exact mul_le_of_le_one_right hbase0 (rpow_neg_le_one_of_one_le hz.le ha)

theorem harperSquarefreeShiftedSmoothEnergy_nonneg
    (y : ℕ) (a : ℝ) (omega : Problem520.Omega) :
    0 ≤ harperSquarefreeShiftedSmoothEnergy y a omega := by
  unfold harperSquarefreeShiftedSmoothEnergy
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
  have hzpos : 0 < z := lt_trans (by norm_num) hz
  exact mul_nonneg (div_nonneg (sq_nonneg _) (sq_nonneg _))
    (Real.rpow_nonneg hzpos.le _)

set_option maxHeartbeats 800000 in
theorem measurable_harperSquarefreeShiftedSmoothEnergy (y : ℕ) (a : ℝ) :
    Measurable fun omega : Problem520.Omega ↦
      harperSquarefreeShiftedSmoothEnergy y a omega := by
  let ν : Measure ℝ := volume.restrict (Set.Ioi (1 : ℝ))
  let F : Problem520.Omega × ℝ → ℝ := fun w ↦
    (|Problem520.ΨReal w.1 w.2 y| ^ 2 / w.2 ^ 2) * w.2 ^ (-a)
  have hswap : Measurable fun w : Problem520.Omega × ℝ ↦ (w.2, w.1) :=
    measurable_snd.prodMk measurable_fst
  have hΨ : Measurable fun w : Problem520.Omega × ℝ ↦
      Problem520.ΨReal w.1 w.2 y :=
    (Problem520.measurable_ΨReal_joint y).comp hswap
  have hF : Measurable F := by
    exact ((hΨ.abs.pow_const 2).div (measurable_snd.pow_const 2)).mul
      (measurable_snd.pow_const (-a))
  have hinner : Measurable fun omega : Problem520.Omega ↦
      ∫ z, F (omega, z) ∂ν :=
    hF.stronglyMeasurable.integral_prod_right.measurable
  simpa only [harperSquarefreeShiftedSmoothEnergy, ν, F] using hinner

/-- Every nonnegative Rankin shift is pointwise dominated by the existing
unshifted full smooth energy.  Hence all previously proved upper fractional
moments remain available without a shifted upper theorem. -/
theorem harperSquarefreeShiftedSmoothEnergy_le_smoothEnergy
    (y : ℕ) (omega : Problem520.Omega) {a : ℝ} (ha : 0 ≤ a) :
    harperSquarefreeShiftedSmoothEnergy y a omega ≤
      Problem520.smoothEnergy omega y := by
  have hshift := integrableOn_harperSquarefreeShiftedSmoothEnergy y omega ha
  have hbaseFull := Problem520.integrableOn_smoothEnergy_integrand omega y
  have hbaseOne := hbaseFull.mono_set
    (Set.Ioi_subset_Ioi (by norm_num : (0 : ℝ) ≤ 1))
  have hfirst : harperSquarefreeShiftedSmoothEnergy y a omega ≤
      ∫ z in Set.Ioi (1 : ℝ),
        |Problem520.ΨReal omega z y| ^ 2 / z ^ 2 := by
    unfold harperSquarefreeShiftedSmoothEnergy
    apply integral_mono_ae hshift hbaseOne
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    have hbase0 : 0 ≤ |Problem520.ΨReal omega z y| ^ 2 / z ^ 2 :=
      div_nonneg (sq_nonneg _) (sq_nonneg _)
    exact mul_le_of_le_one_right hbase0
      (rpow_neg_le_one_of_one_le hz.le ha)
  refine hfirst.trans ?_
  unfold Problem520.smoothEnergy
  apply setIntegral_mono_set hbaseFull
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact div_nonneg (sq_nonneg _) (sq_nonneg _)
  · exact Filter.Eventually.of_forall fun z hz ↦ hz.trans' (by norm_num)

/-- The shifted energy in the same normalization as the completed Harper
half-moment theorem. -/
noncomputable def harperSquarefreeShiftedNormalizedEnergy
    (y : ℕ) (a : ℝ) (omega : Problem520.Omega) : ℝ :=
  (2 * Real.pi) * harperSquarefreeShiftedSmoothEnergy y a omega /
    Real.log (y : ℝ)

theorem harperSquarefreeShiftedNormalizedEnergy_nonneg
    {y : ℕ} (a : ℝ) (hy : 1 < y) (omega : Problem520.Omega) :
    0 ≤ harperSquarefreeShiftedNormalizedEnergy y a omega := by
  unfold harperSquarefreeShiftedNormalizedEnergy
  exact div_nonneg
    (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le)
      (harperSquarefreeShiftedSmoothEnergy_nonneg y a omega))
    (Real.log_pos (by exact_mod_cast hy)).le

theorem measurable_harperSquarefreeShiftedNormalizedEnergy (y : ℕ) (a : ℝ) :
    Measurable fun omega : Problem520.Omega ↦
      harperSquarefreeShiftedNormalizedEnergy y a omega := by
  unfold harperSquarefreeShiftedNormalizedEnergy
  exact ((measurable_harperSquarefreeShiftedSmoothEnergy y a).const_mul
    (2 * Real.pi)).div measurable_const

theorem harperSquarefreeShiftedNormalizedEnergy_le_initial
    {y : ℕ} (a : ℝ) (hy : 1 < y) (ha : 0 ≤ a)
    (omega : Problem520.Omega) :
    harperSquarefreeShiftedNormalizedEnergy y a omega ≤
      Problem520.harperInitialNormalizedEnergy y omega := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy)
  unfold harperSquarefreeShiftedNormalizedEnergy
    Problem520.harperInitialNormalizedEnergy
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left
      (harperSquarefreeShiftedSmoothEnergy_le_smoothEnergy y omega ha)
      (mul_nonneg (by norm_num) Real.pi_pos.le)) hlog.le

theorem integrable_harperSquarefreeShiftedNormalizedEnergy_half
    {y : ℕ} (a : ℝ) (hy : 1 < y) (ha : 0 ≤ a) :
    Integrable (fun omega ↦
      harperSquarefreeShiftedNormalizedEnergy y a omega ^ ((1 : ℝ) / 2))
        Problem520.μ := by
  apply (integrable_harperInitialNormalizedEnergy_half hy).mono'
  · exact ((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1 / 2)).measurable.comp
      (measurable_harperSquarefreeShiftedNormalizedEnergy y a)).aestronglyMeasurable
  · exact ae_of_all _ fun omega ↦ by
      have hZ0 := harperSquarefreeShiftedNormalizedEnergy_nonneg a hy omega
      have hH0 := Problem1144.harperInitialNormalizedEnergy_nonneg hy omega
      have hpow := Real.rpow_le_rpow hZ0
        (harperSquarefreeShiftedNormalizedEnergy_le_initial a hy ha omega)
        (by norm_num : (0 : ℝ) ≤ 1 / 2)
      have hZpow := Real.rpow_nonneg hZ0 ((1 : ℝ) / 2)
      have hHpow := Real.rpow_nonneg hH0 ((1 : ℝ) / 2)
      simpa only [Real.norm_eq_abs, abs_of_nonneg hZpow,
        abs_of_nonneg hHpow] using hpow

theorem integrable_harperSquarefreeShiftedNormalizedEnergy_twoThird
    {y : ℕ} (a : ℝ) (hy : 1 < y) (ha : 0 ≤ a) :
    Integrable (fun omega : Problem520.Omega ↦
      harperSquarefreeShiftedNormalizedEnergy y a omega ^
        Problem520.harperTwoThird) Problem520.μ := by
  let Z : Problem520.Omega → ℝ := fun omega ↦
    harperSquarefreeShiftedNormalizedEnergy y a omega
  let H : Problem520.Omega → ℝ := fun omega ↦
    Problem520.harperInitialNormalizedEnergy y omega
  apply (Problem520.integrable_harperInitialNormalizedEnergy_twoThird hy).mono'
  · exact ((Real.continuous_rpow_const
      (by norm_num [Problem520.harperTwoThird] :
        (0 : ℝ) ≤ Problem520.harperTwoThird)).measurable.comp
      (measurable_harperSquarefreeShiftedNormalizedEnergy y a)).aestronglyMeasurable
  · exact ae_of_all _ fun omega ↦ by
      have hZ0 : 0 ≤ Z omega :=
        harperSquarefreeShiftedNormalizedEnergy_nonneg a hy omega
      have hZH : Z omega ≤ H omega :=
        harperSquarefreeShiftedNormalizedEnergy_le_initial a hy ha omega
      have hH0 : 0 ≤ H omega := hZ0.trans hZH
      have hpow : Z omega ^ Problem520.harperTwoThird ≤
          H omega ^ Problem520.harperTwoThird :=
        Real.rpow_le_rpow hZ0 hZH
          (by norm_num [Problem520.harperTwoThird])
      have hZpow := Real.rpow_nonneg hZ0 Problem520.harperTwoThird
      have hHpow := Real.rpow_nonneg hH0 Problem520.harperTwoThird
      simpa only [Real.norm_eq_abs, abs_of_nonneg hZpow,
        abs_of_nonneg hHpow, Z, H] using hpow

theorem integral_harperSquarefreeShiftedNormalizedEnergy_twoThird_le_of_harperBound
    {C a : ℝ} {Y y : ℕ}
    (hHarper : Problem520.HarperRademacherInitialMomentBound C Y)
    (hY : Y ≤ y) (hy : 2 ≤ y) (ha : 0 ≤ a) :
    (∫ omega,
      harperSquarefreeShiftedNormalizedEnergy y a omega ^
        Problem520.harperTwoThird ∂Problem520.μ) ≤
      C / (1 + Problem520.logLogNat y) ^ ((1 : ℝ) / 3) := by
  have hy1 : 1 < y := by omega
  calc
    (∫ omega,
      harperSquarefreeShiftedNormalizedEnergy y a omega ^
        Problem520.harperTwoThird ∂Problem520.μ) ≤
        ∫ omega,
          Problem520.harperInitialNormalizedEnergy y omega ^
            Problem520.harperTwoThird ∂Problem520.μ := by
      apply integral_mono
        (integrable_harperSquarefreeShiftedNormalizedEnergy_twoThird a hy1 ha)
        (Problem520.integrable_harperInitialNormalizedEnergy_twoThird hy1)
      intro omega
      exact Real.rpow_le_rpow
        (harperSquarefreeShiftedNormalizedEnergy_nonneg a hy1 omega)
        (harperSquarefreeShiftedNormalizedEnergy_le_initial a hy1 ha omega)
        (by norm_num [Problem520.harperTwoThird])
    _ ≤ C / (1 + Problem520.logLogNat y) ^ ((1 : ℝ) / 3) :=
      hHarper y hY hy

/-- Lyapunov/Jensen comparison of the half moment with the `2/3` moment on a
probability space. -/
theorem integral_rpow_half_le_integral_rpow_twoThird_threeQuarter
    {Z : Problem520.Omega → ℝ}
    (hZ0 : ∀ omega, 0 ≤ Z omega)
    (htwo : Integrable (fun omega ↦ Z omega ^ ((2 : ℝ) / 3)) Problem520.μ) :
    (∫ omega, Z omega ^ ((1 : ℝ) / 2) ∂Problem520.μ) ≤
      (∫ omega, Z omega ^ ((2 : ℝ) / 3) ∂Problem520.μ) ^
        ((3 : ℝ) / 4) := by
  let W : Problem520.Omega → ℝ := fun omega ↦ Z omega ^ ((2 : ℝ) / 3)
  have hW0 : ∀ omega, 0 ≤ W omega := fun omega ↦
    Real.rpow_nonneg (hZ0 omega) _
  have hJ := Problem520.integralOn_rpow_le_rpow_integralOn_of_le_one
    (ν := Problem520.μ) (Z := W) (G := Set.univ)
    MeasurableSet.univ (q := (3 : ℝ) / 4) (by norm_num) (by norm_num)
    (by simpa only [W] using htwo) hW0
  have hpow : ∀ omega,
      W omega ^ ((3 : ℝ) / 4) = Z omega ^ ((1 : ℝ) / 2) := by
    intro omega
    simp only [W]
    rw [← Real.rpow_mul (hZ0 omega)]
    norm_num
  simpa only [Measure.restrict_univ, hpow, W] using hJ

/-- The inherited upper `2/3` moment gives the correctly scaled upper half
moment for every nonnegative Rankin shift. -/
theorem integral_harperSquarefreeShiftedNormalizedEnergy_half_le_of_harperBound
    {C a : ℝ} {Y y : ℕ} (hC : 0 ≤ C)
    (hHarper : Problem520.HarperRademacherInitialMomentBound C Y)
    (hY : Y ≤ y) (hy : 4 ≤ y) (ha : 0 ≤ a) :
    (∫ omega,
      harperSquarefreeShiftedNormalizedEnergy y a omega ^ ((1 : ℝ) / 2)
        ∂Problem520.μ) ≤
      C ^ ((3 : ℝ) / 4) *
        harperInitialCriticalScale y ^ ((1 : ℝ) / 2) := by
  have hy1 : 1 < y := by omega
  have htwoInt := integrable_harperSquarefreeShiftedNormalizedEnergy_twoThird
    a hy1 ha
  have hJ := integral_rpow_half_le_integral_rpow_twoThird_threeQuarter
    (fun omega ↦ harperSquarefreeShiftedNormalizedEnergy_nonneg a hy1 omega)
    (by simpa only [Problem520.harperTwoThird] using htwoInt)
  have htwo :=
    integral_harperSquarefreeShiftedNormalizedEnergy_twoThird_le_of_harperBound
      hHarper hY (by omega) ha
  have htwo0 : 0 ≤ ∫ omega,
      harperSquarefreeShiftedNormalizedEnergy y a omega ^
        Problem520.harperTwoThird ∂Problem520.μ :=
    integral_nonneg fun omega ↦ Real.rpow_nonneg
      (harperSquarefreeShiftedNormalizedEnergy_nonneg a hy1 omega) _
  have hraised := Real.rpow_le_rpow htwo0 htwo
    (by norm_num : (0 : ℝ) ≤ 3 / 4)
  refine hJ.trans ?_
  calc
    (∫ omega,
      harperSquarefreeShiftedNormalizedEnergy y a omega ^ ((2 : ℝ) / 3)
        ∂Problem520.μ) ^ ((3 : ℝ) / 4) ≤
        (C / (1 + Problem520.logLogNat y) ^ ((1 : ℝ) / 3)) ^
          ((3 : ℝ) / 4) := by
      simpa only [Problem520.harperTwoThird] using hraised
    _ = C ^ ((3 : ℝ) / 4) *
        harperInitialCriticalScale y ^ ((1 : ℝ) / 2) := by
      have hL : 0 < 1 + Problem520.logLogNat y :=
        Problem520.one_add_logLogNat_pos_of_four_le hy
      unfold harperInitialCriticalScale
      have hD : 0 ≤
          (1 + Problem520.logLogNat y) ^ ((1 : ℝ) / 3) :=
        Real.rpow_nonneg hL.le _
      rw [Real.div_rpow hC hD]
      rw [← Real.rpow_mul hL.le]
      rw [← Real.rpow_mul hL.le]
      rw [div_eq_mul_inv, ← Real.rpow_neg hL.le]
      congr 1 <;> norm_num

/-- The shifted energy splits exactly at the coefficient boundary. -/
theorem harperSquarefreeShiftedSmoothEnergy_eq_prefix_add_tail
    (y : ℕ) (omega : Problem520.Omega) {a : ℝ}
    (hy : 1 ≤ y) (ha : 0 ≤ a) :
    harperSquarefreeShiftedSmoothEnergy y a omega =
      (∫ z in Set.Ioc (1 : ℝ) (y : ℝ),
        (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-a)) +
      ∫ z in Set.Ioi (y : ℝ),
        (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-a) := by
  let f : ℝ → ℝ := fun z ↦
    (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-a)
  have hfull := integrableOn_harperSquarefreeShiftedSmoothEnergy y omega ha
  have hprefix : IntegrableOn f (Set.Ioc (1 : ℝ) (y : ℝ)) :=
    hfull.mono_set (by intro z hz; exact hz.1)
  have htail : IntegrableOn f (Set.Ioi (y : ℝ)) :=
    hfull.mono_set (Set.Ioi_subset_Ioi (by exact_mod_cast hy))
  have hdisjoint : Disjoint (Set.Ioc (1 : ℝ) (y : ℝ))
      (Set.Ioi (y : ℝ)) := by
    rw [Set.disjoint_left]
    intro z hzPrefix hzTail
    exact (not_lt_of_ge hzPrefix.2) hzTail
  have hunion : Set.Ioc (1 : ℝ) (y : ℝ) ∪ Set.Ioi (y : ℝ) =
      Set.Ioi (1 : ℝ) := by
    have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
    rw [Set.Ioc_union_Ioi (show (y : ℝ) ≤ max (1 : ℝ) y by simp [hyR])]
    simp [hyR]
  unfold harperSquarefreeShiftedSmoothEnergy
  rw [← hunion]
  exact setIntegral_union hdisjoint measurableSet_Ioi hprefix htail

/-- On the prefix, adding a nonnegative shift only decreases the energy. -/
theorem harperSquarefreeShiftedPrefix_le_prefixEnergy
    (y : ℕ) (omega : Problem520.Omega) {a : ℝ}
    (ha : 0 ≤ a) :
    (∫ z in Set.Ioc (1 : ℝ) (y : ℝ),
      (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-a)) ≤
      harperSquarefreeCoefficientPrefixEnergy y omega := by
  unfold harperSquarefreeCoefficientPrefixEnergy
  apply integral_mono_ae
    ((integrableOn_harperSquarefreeShiftedSmoothEnergy y omega ha).mono_set
      (by intro z hz; exact hz.1))
    (integrableOn_harperSquarefreeCoefficientPrefixEnergy y omega)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with z hz
  have hbase0 : 0 ≤ |Problem520.ΨReal omega z y| ^ 2 / z ^ 2 :=
    div_nonneg (sq_nonneg _) (sq_nonneg _)
  exact mul_le_of_le_one_right hbase0
    (rpow_neg_le_one_of_one_le hz.1.le ha)

/-- Beyond `y`, half of the shift can be frozen at the boundary. -/
theorem harperSquarefreeShiftedTail_le_boundary_mul_halfShift
    (y : ℕ) (omega : Problem520.Omega) {a : ℝ}
    (hy : 1 ≤ y) (ha : 0 ≤ a) :
    (∫ z in Set.Ioi (y : ℝ),
      (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-a)) ≤
      (y : ℝ) ^ (-(a / 2)) * harperSquarefreeShiftedSmoothEnergy y (a / 2) omega := by
  have hhalf : 0 ≤ a / 2 := by positivity
  have hfullHalf := integrableOn_harperSquarefreeShiftedSmoothEnergy y omega hhalf
  have hyR : (1 : ℝ) ≤ (y : ℝ) := by exact_mod_cast hy
  have htailA := (integrableOn_harperSquarefreeShiftedSmoothEnergy y omega ha).mono_set
    (Set.Ioi_subset_Ioi hyR)
  have htailHalf := hfullHalf.mono_set
    (Set.Ioi_subset_Ioi hyR)
  calc
    (∫ z in Set.Ioi (y : ℝ),
      (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-a)) ≤
        ∫ z in Set.Ioi (y : ℝ),
          (y : ℝ) ^ (-(a / 2)) *
            ((|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-(a / 2))) := by
      apply integral_mono_ae htailA
        (htailHalf.const_mul ((y : ℝ) ^ (-(a / 2))))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
      have hyRpos : (0 : ℝ) < y := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hy)
      have hzpos : 0 < z := hyRpos.trans hz
      have hbase0 : 0 ≤ |Problem520.ΨReal omega z y| ^ 2 / z ^ 2 :=
        div_nonneg (sq_nonneg _) (sq_nonneg _)
      have hzhalf0 : 0 ≤ z ^ (-(a / 2)) := Real.rpow_nonneg hzpos.le _
      have hboundary : z ^ (-(a / 2)) ≤ (y : ℝ) ^ (-(a / 2)) :=
        Real.rpow_le_rpow_of_nonpos hyRpos (le_of_lt hz) (neg_nonpos.mpr hhalf)
      rw [show -a = -(a / 2) + -(a / 2) by ring,
        Real.rpow_add hzpos]
      calc
        |Problem520.ΨReal omega z y| ^ 2 / z ^ 2 *
            (z ^ (-(a / 2)) * z ^ (-(a / 2))) =
            z ^ (-(a / 2)) *
              ((|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) *
                z ^ (-(a / 2))) := by ring
        _ ≤ (y : ℝ) ^ (-(a / 2)) *
              ((|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) *
                z ^ (-(a / 2))) :=
          mul_le_mul_of_nonneg_right hboundary (mul_nonneg hbase0 hzhalf0)
    _ = (y : ℝ) ^ (-(a / 2)) *
        (∫ z in Set.Ioi (y : ℝ),
          (|Problem520.ΨReal omega z y| ^ 2 / z ^ 2) * z ^ (-(a / 2))) := by
      rw [← integral_const_mul]
    _ ≤ (y : ℝ) ^ (-(a / 2)) *
        harperSquarefreeShiftedSmoothEnergy y (a / 2) omega := by
      gcongr
      unfold harperSquarefreeShiftedSmoothEnergy
      apply setIntegral_mono_set hfullHalf
      · filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
        have hzpos : 0 < z := lt_trans (by norm_num) hz
        exact mul_nonneg
          (div_nonneg (sq_nonneg _) (sq_nonneg _))
          (Real.rpow_nonneg hzpos.le _)
      · exact Filter.Eventually.of_forall fun z hz ↦
          hyR.trans_lt hz

theorem harperSquarefreePrefixEnergy_ge_shifted_sub_boundary
    (y : ℕ) (omega : Problem520.Omega) {a : ℝ}
    (hy : 2 ≤ y) (ha : 0 ≤ a) :
    harperSquarefreeShiftedSmoothEnergy y a omega -
        (y : ℝ) ^ (-(a / 2)) *
          harperSquarefreeShiftedSmoothEnergy y (a / 2) omega ≤
      harperSquarefreeCoefficientPrefixEnergy y omega := by
  have hsplit := harperSquarefreeShiftedSmoothEnergy_eq_prefix_add_tail
    y omega (by omega) ha
  have hprefix := harperSquarefreeShiftedPrefix_le_prefixEnergy y omega ha
  have htail := harperSquarefreeShiftedTail_le_boundary_mul_halfShift
    y omega (by omega) ha
  linarith

/-- On the Harper scale `a = 4V / log y`, the boundary loss is exactly
`exp (-2V)`. -/
theorem harperRankinBoundaryWeight_eq_exp
    (y : ℕ) (V : ℝ) (hy : 1 < y) :
    (y : ℝ) ^ (-((4 * V / Real.log (y : ℝ)) / 2)) =
      Real.exp (-2 * V) := by
  have hyR : (0 : ℝ) < y := by exact_mod_cast Nat.zero_lt_of_lt hy
  have hlog : Real.log (y : ℝ) ≠ 0 :=
    (Real.log_pos (by exact_mod_cast hy)).ne'
  rw [Real.rpow_def_of_pos hyR]
  congr 1
  field_simp
  ring

/-- Exact Harper localization with the conventional shift parameter. -/
theorem harperSquarefreePrefixEnergy_ge_rankinShift_sub_exp
    (y : ℕ) (omega : Problem520.Omega) {V : ℝ}
    (hy : 2 ≤ y) (hV : 0 ≤ V) :
    harperSquarefreeShiftedSmoothEnergy y
          (4 * V / Real.log (y : ℝ)) omega -
        Real.exp (-2 * V) *
          harperSquarefreeShiftedSmoothEnergy y
            ((4 * V / Real.log (y : ℝ)) / 2) omega ≤
      harperSquarefreeCoefficientPrefixEnergy y omega := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have ha : 0 ≤ 4 * V / Real.log (y : ℝ) := by positivity
  have hmain := harperSquarefreePrefixEnergy_ge_shifted_sub_boundary
    y omega hy ha
  rw [harperRankinBoundaryWeight_eq_exp y V (by omega)] at hmain
  exact hmain

private theorem sqrt_le_sqrt_add_sqrt_of_le_add
    {A P Q : ℝ} (hA : 0 ≤ A) (hP : 0 ≤ P) (hQ : 0 ≤ Q)
    (h : A ≤ P + Q) :
    Real.sqrt A ≤ Real.sqrt P + Real.sqrt Q := by
  rw [Real.sqrt_le_left
    (add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))]
  nlinarith [Real.sq_sqrt hA, Real.sq_sqrt hP, Real.sq_sqrt hQ,
    mul_nonneg (Real.sqrt_nonneg P) (Real.sqrt_nonneg Q)]

private theorem sqrt_exp_neg_two_mul (V : ℝ) :
    Real.sqrt (Real.exp (-2 * V)) = Real.exp (-V) := by
  calc
    Real.sqrt (Real.exp (-2 * V)) =
        Real.sqrt ((Real.exp (-V)) ^ 2) := by
      congr 1
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    _ = |Real.exp (-V)| := Real.sqrt_sq_eq_abs _
    _ = Real.exp (-V) := abs_of_pos (Real.exp_pos _)

/-- Normalized pointwise form of the Rankin localization. -/
theorem harperSquarefreeNormalizedPrefix_ge_rankinShift_sub_exp
    (y : ℕ) (omega : Problem520.Omega) {V : ℝ}
    (hy : 2 ≤ y) (hV : 0 ≤ V) :
    harperSquarefreeShiftedNormalizedEnergy y
          (4 * V / Real.log (y : ℝ)) omega -
        Real.exp (-2 * V) *
          harperSquarefreeShiftedNormalizedEnergy y
            ((4 * V / Real.log (y : ℝ)) / 2) omega ≤
      harperSquarefreeCoefficientNormalizedEnergy y omega := by
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  let scale : ℝ := 2 * Real.pi / Real.log (y : ℝ)
  have hscale : 0 ≤ scale := by
    exact div_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hlog.le
  have hmain := harperSquarefreePrefixEnergy_ge_rankinShift_sub_exp
    y omega hy hV
  have hscaled := mul_le_mul_of_nonneg_left hmain hscale
  simpa only [harperSquarefreeShiftedNormalizedEnergy,
    harperSquarefreeCoefficientNormalizedEnergy, scale] using (by
      convert hscaled using 1 <;> ring)

/-- At the half-moment level, the exponentially damped Rankin tail costs only
`exp (-V)`. -/
theorem rankinShiftedNormalizedEnergy_half_le_prefix_add_tail
    (y : ℕ) (omega : Problem520.Omega) {V : ℝ}
    (hy : 2 ≤ y) (hV : 0 ≤ V) :
    harperSquarefreeShiftedNormalizedEnergy y
          (4 * V / Real.log (y : ℝ)) omega ^ ((1 : ℝ) / 2) ≤
      harperSquarefreeCoefficientNormalizedEnergy y omega ^ ((1 : ℝ) / 2) +
        Real.exp (-V) *
          harperSquarefreeShiftedNormalizedEnergy y
            ((4 * V / Real.log (y : ℝ)) / 2) omega ^ ((1 : ℝ) / 2) := by
  let A := harperSquarefreeShiftedNormalizedEnergy y
    (4 * V / Real.log (y : ℝ)) omega
  let P := harperSquarefreeCoefficientNormalizedEnergy y omega
  let B := harperSquarefreeShiftedNormalizedEnergy y
    ((4 * V / Real.log (y : ℝ)) / 2) omega
  let Q := Real.exp (-2 * V) * B
  have hy1 : 1 < y := by omega
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy1)
  have ha : 0 ≤ 4 * V / Real.log (y : ℝ) := by positivity
  have hhalf : 0 ≤ (4 * V / Real.log (y : ℝ)) / 2 := by positivity
  have hA : 0 ≤ A :=
    harperSquarefreeShiftedNormalizedEnergy_nonneg _ hy1 omega
  have hP : 0 ≤ P :=
    harperSquarefreeCoefficientNormalizedEnergy_nonneg hy1 omega
  have hB : 0 ≤ B :=
    harperSquarefreeShiftedNormalizedEnergy_nonneg _ hy1 omega
  have hQ : 0 ≤ Q := mul_nonneg (Real.exp_pos _).le hB
  have hloc : A ≤ P + Q := by
    have h := harperSquarefreeNormalizedPrefix_ge_rankinShift_sub_exp
      y omega hy hV
    dsimp only [A, P, B, Q]
    linarith
  have hsqrt := sqrt_le_sqrt_add_sqrt_of_le_add hA hP hQ hloc
  rw [Real.sqrt_mul (Real.exp_pos _).le,
    sqrt_exp_neg_two_mul] at hsqrt
  simpa only [A, P, B, Q, Real.sqrt_eq_rpow] using hsqrt

/-- Integrated half-moment transfer.  This is the exact final analytic
interface: a shifted lower half moment minus an `exp (-V)` multiple of an
already-controlled shifted upper half moment yields the desired prefix lower
half moment. -/
theorem integral_rankinShiftedNormalizedEnergy_half_le_prefix_add_tail
    (y : ℕ) {V : ℝ} (hy : 2 ≤ y) (hV : 0 ≤ V) :
    (∫ omega,
      harperSquarefreeShiftedNormalizedEnergy y
        (4 * V / Real.log (y : ℝ)) omega ^ ((1 : ℝ) / 2)
        ∂Problem520.μ) ≤
      (∫ omega,
        harperSquarefreeCoefficientNormalizedEnergy y omega ^ ((1 : ℝ) / 2)
          ∂Problem520.μ) +
      Real.exp (-V) *
        ∫ omega,
          harperSquarefreeShiftedNormalizedEnergy y
            ((4 * V / Real.log (y : ℝ)) / 2) omega ^ ((1 : ℝ) / 2)
            ∂Problem520.μ := by
  have hy1 : 1 < y := by omega
  have hlog : 0 < Real.log (y : ℝ) :=
    Real.log_pos (by exact_mod_cast hy1)
  have ha : 0 ≤ 4 * V / Real.log (y : ℝ) := by positivity
  have hhalf : 0 ≤ (4 * V / Real.log (y : ℝ)) / 2 := by positivity
  have hA := integrable_harperSquarefreeShiftedNormalizedEnergy_half
    (4 * V / Real.log (y : ℝ)) hy1 ha
  have hP := integrable_harperSquarefreeCoefficientNormalizedEnergy_half hy1
  have hB := integrable_harperSquarefreeShiftedNormalizedEnergy_half
    ((4 * V / Real.log (y : ℝ)) / 2) hy1 hhalf
  calc
    (∫ omega,
      harperSquarefreeShiftedNormalizedEnergy y
        (4 * V / Real.log (y : ℝ)) omega ^ ((1 : ℝ) / 2)
        ∂Problem520.μ) ≤
        ∫ omega,
          harperSquarefreeCoefficientNormalizedEnergy y omega ^ ((1 : ℝ) / 2) +
            Real.exp (-V) *
              harperSquarefreeShiftedNormalizedEnergy y
                ((4 * V / Real.log (y : ℝ)) / 2) omega ^ ((1 : ℝ) / 2)
          ∂Problem520.μ := by
      apply integral_mono hA (hP.add (hB.const_mul (Real.exp (-V))))
      intro omega
      exact rankinShiftedNormalizedEnergy_half_le_prefix_add_tail
        y omega hy hV
    _ = _ := by
      rw [integral_add hP (hB.const_mul (Real.exp (-V))), integral_const_mul]

/-! ## The single remaining shifted-ballot checkpoint -/

/-- Lower half moment for the Rankin-shifted energy at one fixed damping
parameter `V`. -/
def HarperRankinShiftedHalfMomentLowerBound
    (V c : ℝ) (Y : ℕ) : Prop :=
  ∀ y : ℕ, Y ≤ y → 4 ≤ y →
    c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2) ≤
      ∫ omega,
        harperSquarefreeShiftedNormalizedEnergy y
          (4 * V / Real.log (y : ℝ)) omega ^ ((1 : ℝ) / 2)
          ∂Problem520.μ

/-- Exact analytic statement still required.  The quantifier over the known
upper-moment constant lets `V` be chosen after that constant; the exponential
Rankin tail must consume at most half of the shifted lower constant. -/
def HarperRankinShiftedHalfMomentLowerStatement : Prop :=
  ∀ C : ℝ, 0 < C →
    ∃ V c : ℝ, 0 ≤ V ∧ 0 < c ∧
      Real.exp (-V) * C ^ ((3 : ℝ) / 4) ≤ c / 2 ∧
      ∃ Y : ℕ, HarperRankinShiftedHalfMomentLowerBound V c Y

/-- The shifted-ballot checkpoint, together with the already unconditional
upper `2/3` moment, implies the coefficient-prefix half moment.  All Rankin
localization and tail absorption are discharged here. -/
theorem harperSquarefreeCoefficientHalfMomentLowerStatement_of_rankinShifted
    (hshift : HarperRankinShiftedHalfMomentLowerStatement) :
    HarperSquarefreeCoefficientHalfMomentLowerStatement := by
  obtain ⟨C, hC, Ytwo, _hYtwo, htwo⟩ :=
    Problem520.harperRademacherInitialMomentStatement_unconditional
  obtain ⟨V, c, hV, hc, habsorb, Yshift, hshiftLower⟩ := hshift C hC
  let d : ℝ := c / 2
  have hd : 0 < d := div_pos hc (by norm_num)
  refine ⟨d, hd, max Yshift Ytwo, ?_⟩
  intro y hyY hy4
  have hyShift : Yshift ≤ y := (le_max_left _ _).trans hyY
  have hyTwo : Ytwo ≤ y := (le_max_right _ _).trans hyY
  let K : ℝ := harperInitialCriticalScale y ^ ((1 : ℝ) / 2)
  let A : ℝ := ∫ omega,
    harperSquarefreeShiftedNormalizedEnergy y
      (4 * V / Real.log (y : ℝ)) omega ^ ((1 : ℝ) / 2)
      ∂Problem520.μ
  let P : ℝ := ∫ omega,
    harperSquarefreeCoefficientNormalizedEnergy y omega ^ ((1 : ℝ) / 2)
      ∂Problem520.μ
  let B : ℝ := ∫ omega,
    harperSquarefreeShiftedNormalizedEnergy y
      ((4 * V / Real.log (y : ℝ)) / 2) omega ^ ((1 : ℝ) / 2)
      ∂Problem520.μ
  have hK : 0 ≤ K := Real.rpow_nonneg
    (harperInitialCriticalScale_pos hy4).le _
  have hLower : c * K ≤ A := by
    simpa only [A, K] using hshiftLower y hyShift hy4
  have hTransfer : A ≤ P + Real.exp (-V) * B := by
    simpa only [A, P, B] using
      integral_rankinShiftedNormalizedEnergy_half_le_prefix_add_tail
        y (by omega) hV
  have hTail : B ≤ C ^ ((3 : ℝ) / 4) * K := by
    have hlog : 0 < Real.log (y : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    have ha : 0 ≤ (4 * V / Real.log (y : ℝ)) / 2 := by positivity
    simpa only [B, K] using
      integral_harperSquarefreeShiftedNormalizedEnergy_half_le_of_harperBound
        hC.le htwo hyTwo hy4 ha
  have hExp : 0 ≤ Real.exp (-V) := (Real.exp_pos _).le
  have hTailScaled : Real.exp (-V) * B ≤ (c / 2) * K := by
    calc
      Real.exp (-V) * B ≤
          Real.exp (-V) * (C ^ ((3 : ℝ) / 4) * K) :=
        mul_le_mul_of_nonneg_left hTail hExp
      _ = (Real.exp (-V) * C ^ ((3 : ℝ) / 4)) * K := by ring
      _ ≤ (c / 2) * K := mul_le_mul_of_nonneg_right habsorb hK
  change d * K ≤ P
  dsimp only [d]
  linarith

/-- Complete probability handoff from the single Rankin-shifted ballot
checkpoint.  No further localization or fractional-moment input is required
after this theorem. -/
theorem exists_harperSquarefreeCoefficientCriticalEnergy_fixedProbability_of_rankinShifted
    (hshift : HarperRankinShiftedHalfMomentLowerStatement) :
    ∃ delta : ℝ, 0 < delta ∧ ∃ c : ℝ, 0 < c ∧ ∃ Y : ℕ, ∀ y : ℕ,
      Y ≤ y →
      delta ≤ Problem520.μ.real
        (halfMomentLargeEvent
          (harperSquarefreeCoefficientNormalizedEnergy y)
          (c * harperInitialCriticalScale y ^ ((1 : ℝ) / 2))) :=
  exists_harperSquarefreeCoefficientCriticalEnergy_fixedProbability
    (harperSquarefreeCoefficientHalfMomentLowerStatement_of_rankinShifted hshift)

end Problem1144
end Erdos

#print axioms Erdos.Problem1144.harperSquarefreePrefixEnergy_ge_shifted_sub_boundary
#print axioms Erdos.Problem1144.harperSquarefreeShiftedSmoothEnergy_le_smoothEnergy
#print axioms Erdos.Problem1144.harperRankinBoundaryWeight_eq_exp
#print axioms Erdos.Problem1144.harperSquarefreePrefixEnergy_ge_rankinShift_sub_exp
#print axioms Erdos.Problem1144.integral_harperSquarefreeShiftedNormalizedEnergy_half_le_of_harperBound
#print axioms Erdos.Problem1144.integral_rankinShiftedNormalizedEnergy_half_le_prefix_add_tail
#print axioms Erdos.Problem1144.harperSquarefreeCoefficientHalfMomentLowerStatement_of_rankinShifted
#print axioms Erdos.Problem1144.exists_harperSquarefreeCoefficientCriticalEnergy_fixedProbability_of_rankinShifted
