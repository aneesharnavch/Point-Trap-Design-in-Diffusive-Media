module

public import TimeTraps.Probability.GraphAtomicSurvivalIntegrability

@[expose] public section

/-! The finite Dynkin identity and positivity of the original weak state
force an explicit inverse-time bound for survival. No almost-sure killing
or finite expected lifetime is assumed in deriving this estimate. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal Topology

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

set_option backward.isDefEq.respectTransparency false

theorem GraphShiftedContactOperatorProblem.atomicRunningCost_path_lower_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    ∀ᵐ p ∂P.continuousPathLaw h0 x,
      ((T : ℝ) * (P.geometry.physicalSpeedLower b hb : ℝ)) * P.atomicSurvival a κ T p ≤
        ∫ r in Ioc (0 : ℝ) (T : ℝ), P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal) := by
  filter_upwards [P.atomicSurvival_antitone_ae h0 x a κ hκ] with p hp
  calc
    _ = ∫ _r in Ioc (0 : ℝ) (T : ℝ),
        P.atomicSurvival a κ T p * (P.geometry.physicalSpeedLower b hb : ℝ) := by
      rw [setIntegral_const, Real.volume_real_Ioc_of_le T.coe_nonneg, sub_zero, smul_eq_mul]
      ring
    _ ≤ _ := integral_mono_ae (integrable_const _) (P.atomicRunningCost_path_integrable b hb a κ hκ T p)
      (by
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        exact mul_le_mul (hp (Real.toNNReal_le_iff_le_coe.mpr hr.2))
          (P.geometry.physicalSpeed_bound b hb (p r.toNNReal)).1
          (NNReal.coe_nonneg _) (P.atomicSurvival_bounds a κ hκ r.toNNReal p).1.le)

theorem GraphShiftedContactOperatorProblem.atomicSurvival_mul_le_of_martingale
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (u : C(GraphRealization P.geometry, ℝ)) (hu : ∀ y, 0 ≤ u y)
    (hM : Martingale (P.atomicCompensatedProcess b hb a κ u)
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw h0 x)) (T : ℝ≥0) :
    ((T : ℝ) * (P.geometry.physicalSpeedLower b hb : ℝ)) *
      (∫ p, P.atomicSurvival a κ T p ∂P.continuousPathLaw h0 x) ≤ u x := by
  have hC := P.atomicRunningCost_finite_of_martingale h0 x b hb a κ hκ u hM T
  have hle := integral_mono_ae
    ((P.atomicSurvival_integrable h0 x a κ hκ T).const_mul ((T : ℝ) * (P.geometry.physicalSpeedLower b hb : ℝ)))
    hC.1 (P.atomicRunningCost_path_lower_ae h0 x b hb a κ hκ T)
  rw [integral_const_mul, hC.2] at hle
  have hn : 0 ≤ ∫ p, P.atomicSurvival a κ T p * u (p T) ∂P.continuousPathLaw h0 x :=
    integral_nonneg (fun p => mul_nonneg (P.atomicSurvival_bounds a κ hκ T p).1.le (hu (p T)))
  linarith

theorem GraphShiftedContactOperatorProblem.atomicSurvival_tendsto_zero_of_martingale
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (u : C(GraphRealization P.geometry, ℝ)) (hu : ∀ y, 0 ≤ u y)
    (hM : Martingale (P.atomicCompensatedProcess b hb a κ u)
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw h0 x)) :
    Tendsto (fun T : ℝ≥0 => ∫ p, P.atomicSurvival a κ T p ∂P.continuousPathLaw h0 x) atTop (𝓝 0) := by
  let m : ℝ := P.geometry.physicalSpeedLower b hb
  have hm : 0 < m := P.geometry.physicalSpeedLower_pos b hb
  have ht : Tendsto (fun T : ℝ≥0 => (T : ℝ)) atTop atTop := NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hd : Tendsto (fun T : ℝ≥0 => (u x / m) / (T : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero, Function.comp_apply] using
      (tendsto_inv_atTop_zero.comp ht).const_mul (u x / m)
  apply squeeze_zero' (Eventually.of_forall (fun T =>
    integral_nonneg (fun p => (P.atomicSurvival_bounds a κ hκ T p).1.le))) _ hd
  filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with T hT
  apply (le_div_iff₀ (show (0 : ℝ) < T from hT)).mpr
  apply (le_div_iff₀ hm).mpr
  have hl := P.atomicSurvival_mul_le_of_martingale h0 x b hb a κ hκ u hu hM T
  simpa only [m, mul_assoc, mul_comm, mul_left_comm] using hl

theorem GraphShiftedContactOperatorProblem.atomicSurvival_observation_tendsto_zero_of_martingale
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (u : C(GraphRealization P.geometry, ℝ)) (hu : ∀ y, 0 ≤ u y)
    (hM : Martingale (P.atomicCompensatedProcess b hb a κ u)
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw h0 x)) :
    Tendsto (fun T : ℝ≥0 => ∫ p, P.atomicSurvival a κ T p * u (p T) ∂P.continuousPathLaw h0 x) atTop (𝓝 0) := by
  have hbnd (T : ℝ≥0) : (∫ p, P.atomicSurvival a κ T p * u (p T) ∂P.continuousPathLaw h0 x) ≤
      ‖u‖ * ∫ p, P.atomicSurvival a κ T p ∂P.continuousPathLaw h0 x := by
    rw [← integral_const_mul]
    apply integral_mono (P.atomicSurvival_observation_integrable h0 x a κ hκ u T)
      ((P.atomicSurvival_integrable h0 x a κ hκ T).const_mul ‖u‖)
    intro p
    calc
      _ ≤ P.atomicSurvival a κ T p * ‖u‖ := mul_le_mul_of_nonneg_left
        ((le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using u.norm_coe_le_norm (p T)))
        (P.atomicSurvival_bounds a κ hκ T p).1.le
      _ = _ := mul_comm _ _
  apply squeeze_zero (fun T => integral_nonneg (fun p =>
    mul_nonneg (P.atomicSurvival_bounds a κ hκ T p).1.le (hu (p T)))) hbnd
  simpa only [mul_zero] using
    (P.atomicSurvival_tendsto_zero_of_martingale h0 x b hb a κ hκ u hu hM).const_mul ‖u‖

end TimeTraps.Analysis
