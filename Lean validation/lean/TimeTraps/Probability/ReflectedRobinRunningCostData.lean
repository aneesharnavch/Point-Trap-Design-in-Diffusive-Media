module

public import TimeTraps.Probability.ReflectedRobinWeakData
public import TimeTraps.Probability.ReflectedAtomicWeightedValueTime

@[expose] public section

/-! Continuous signed tests on the physical closed interval have actual
measurability and finite-time integrability for any finite reaction
family, including endpoint labels. No regularity outside the reflected
range is imposed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {g : ℝ → ℝ}

theorem reflectedRobinRunningCost_extension (L : ℝ) (hL : 0 < L) (D : ℝ) (_hD : 0 < D)
    (a κ : ι → ℝ) (_hκ : ∀ i, 0 ≤ κ i)
    (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedAtomicWeightedValue
      (reflectedFellerExtension L hL (reflectedRobinKinkSource L g hg))
      L D x a κ T ω =
      reflectedAtomicWeightedValue g L D x a κ T ω := by
  unfold reflectedAtomicWeightedValue
  rw [reflectedRobinKinkSource_extension hL hg
    (foldedTrajectory_mem L hL D x brownianDyadicPath T ω)]

theorem reflectedRobinRunningCost_jointlyMeasurable (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) =>
      reflectedAtomicWeightedValue g L D x a κ p.1 p.2) := by
  have he : (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedAtomicWeightedValue
      (reflectedFellerExtension L hL (reflectedRobinKinkSource L g hg))
      L D x a κ p.1 p.2) =
      (fun p => reflectedAtomicWeightedValue g L D x a κ p.1 p.2) :=
    funext (fun p => reflectedRobinRunningCost_extension L hL D hD a κ hκ hg x p.1 p.2)
  rw [← he]
  exact reflectedAtomicWeightedValue_jointlyMeasurable
    (reflectedFellerExtension L hL (reflectedRobinKinkSource L g hg)).continuous
    L D x a κ

theorem reflectedRobinRunningCost_memLp (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) (T : ℝ≥0) :
    MemLp (reflectedAtomicWeightedValue g L D x a κ T)
      2 brownianDyadicMeasure := by
  apply (reflectedAtomicWeightedValue_memLp
    (reflectedFellerExtension L hL (reflectedRobinKinkSource L g hg)).continuous
    L hL D hD x a κ
    hκ T).ae_eq
  exact Eventually.of_forall (reflectedRobinRunningCost_extension L hL D hD a κ hκ hg x T)

theorem reflectedRobinRunningCost_time_joint_integrable (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) (T : ℝ≥0) :
    Integrable (fun p : ℝ × (ℕ → ℝ) =>
      reflectedAtomicWeightedValue g L D x a κ p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
  apply (reflectedAtomicWeightedValue_time_joint_integrable
    (reflectedFellerExtension L hL (reflectedRobinKinkSource L g hg)).continuous
    L hL D hD x a κ
    hκ T).congr
  exact Eventually.of_forall (fun p => reflectedRobinRunningCost_extension L hL D hD a κ hκ hg x p.1.toNNReal p.2)

theorem reflectedRobinRunningCost_time_integral_integrable (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..T.val,
      reflectedAtomicWeightedValue g L D x a κ r.toNNReal ω)
      brownianDyadicMeasure := by
  apply (reflectedRobinRunningCost_time_joint_integrable L hL D hD a κ hκ hg x T).integral_prod_right.congr
  exact Eventually.of_forall (fun _ => (intervalIntegral.integral_of_le T.coe_nonneg).symm)

theorem reflectedRobinRunningCost_mean_time_integral (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicWeightedValue g L D x a κ r.toNNReal ω)
      ∂brownianDyadicMeasure) =
      ∫ r in (0 : ℝ)..T.val,
        reflectedAtomicValueExpectation g L D x a κ r.toNNReal := by
  calc
    _ = ∫ ω, (∫ r in Ioc (0 : ℝ) T.val,
        reflectedAtomicWeightedValue g L D x a κ r.toNNReal ω)
        ∂brownianDyadicMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun _ => intervalIntegral.integral_of_le T.coe_nonneg)
    _ = ∫ r in Ioc (0 : ℝ) T.val,
        reflectedAtomicValueExpectation g L D x a κ r.toNNReal :=
      (integral_integral_swap (reflectedRobinRunningCost_time_joint_integrable L hL D hD a κ hκ hg x T)).symm
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem reflectedRobinRunningCost_expectation_continuous (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) :
    Continuous (reflectedAtomicValueExpectation g L D x a κ) := by
  have he : reflectedAtomicValueExpectation
      (reflectedFellerExtension L hL (reflectedRobinKinkSource L g hg))
      L D x a κ =
      reflectedAtomicValueExpectation g L D x a κ := by
    funext T
    exact integral_congr_ae (Eventually.of_forall (reflectedRobinRunningCost_extension L hL D hD a κ hκ hg x T))
  rw [← he]
  exact reflectedAtomicValueExpectation_continuous
    (reflectedFellerExtension L hL (reflectedRobinKinkSource L g hg)).continuous
    L hL D hD x a κ
    hκ

theorem reflectedRobinRunningCost_integral_norm_le (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hg : ContinuousOn g (Icc 0 L)) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, ‖reflectedAtomicWeightedValue g L D x a κ T ω‖
      ∂brownianDyadicMeasure) ≤
      ‖reflectedRobinKinkSource L g hg‖ *
        reflectedAtomicMeanSurvival L D x a κ T := by
  rw [reflectedAtomicMeanSurvival, ← integral_const_mul]
  apply integral_mono ((reflectedRobinRunningCost_memLp L hL D hD a κ hκ hg x T).integrable (by norm_num)).norm
    ((reflectedAtomicSurvival_integrable L hD x a κ
      hκ T).const_mul _)
  intro ω
  have hw := (reflectedAtomicSurvival_bounds L hD x a κ
    hκ T ω).1
  have hb := (reflectedRobinKinkSource L g hg).norm_coe_le_norm
    ⟨_, foldedTrajectory_mem L hL D x brownianDyadicPath T ω⟩
  change ‖g (foldedTrajectory L D x brownianDyadicPath T ω)‖ ≤ _ at hb
  change ‖reflectedAtomicSurvival L D x a κ T ω *
    g (foldedTrajectory L D x brownianDyadicPath T ω)‖ ≤
      ‖reflectedRobinKinkSource L g hg‖ * reflectedAtomicSurvival L D x a κ T ω
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hw]
  exact (mul_le_mul_of_nonneg_left hb hw.le).trans_eq (mul_comm _ _)

end TimeTraps.Probability
