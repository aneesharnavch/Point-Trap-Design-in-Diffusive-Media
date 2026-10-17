module

public import TimeTraps.Probability.GraphAtomicSurvivalTailBound
public import TimeTraps.Probability.NonnegativeRunningCostLimit

@[expose] public section

/-! The actual nonnegative running cost has finite total expectation
and equals the original positive state once its compensated expression
is a martingale. Infinite horizons follow by monotone convergence. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal Topology

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.atomicRunningCost_finite_lintegral_of_martingale
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (u : C(GraphRealization P.geometry, ℝ))
    (hM : Martingale (P.atomicCompensatedProcess b hb a κ u)
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw h0 x)) (T : ℝ≥0) :
    (∫⁻ p, (∫⁻ r in Ioc (0 : ℝ) (T : ℝ), ENNReal.ofReal
      (P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal))) ∂P.continuousPathLaw h0 x) =
      ENNReal.ofReal (u x - ∫ p, P.atomicSurvival a κ T p * u (p T) ∂P.continuousPathLaw h0 x) := by
  let f := fun (r : ℝ) (p : GraphContinuousPath P.geometry) =>
    P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal)
  have hn (r : ℝ) (p : GraphContinuousPath P.geometry) : 0 ≤ f r p :=
    mul_nonneg (P.atomicSurvival_bounds a κ hκ r.toNNReal p).1.le
      ((NNReal.coe_nonneg _).trans (P.geometry.physicalSpeed_bound b hb (p r.toNNReal)).1)
  have he (p : GraphContinuousPath P.geometry) :
      (∫⁻ r in Ioc (0 : ℝ) (T : ℝ), ENNReal.ofReal (f r p)) =
        ENNReal.ofReal (∫ r in Ioc (0 : ℝ) (T : ℝ), f r p) :=
    (ofReal_integral_eq_lintegral_ofReal (P.atomicRunningCost_path_integrable b hb a κ hκ T p)
      (Eventually.of_forall (fun r => hn r p))).symm
  have hC := P.atomicRunningCost_finite_of_martingale h0 x b hb a κ hκ u hM T
  change (∫⁻ p, (∫⁻ r in Ioc (0 : ℝ) (T : ℝ), ENNReal.ofReal (f r p)) ∂P.continuousPathLaw h0 x) = _
  simp_rw [he]
  rw [← ofReal_integral_eq_lintegral_ofReal hC.1
    (Eventually.of_forall (fun p => integral_nonneg (fun r => hn r p))), hC.2]

theorem GraphShiftedContactOperatorProblem.atomicRunningCost_infinite_of_martingale
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (u : C(GraphRealization P.geometry, ℝ)) (hu : ∀ y, 0 ≤ u y)
    (hM : Martingale (P.atomicCompensatedProcess b hb a κ u)
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw h0 x)) :
    (∫⁻ p, (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal
      (P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal))) ∂P.continuousPathLaw h0 x) =
      ENNReal.ofReal (u x) := by
  have hm := (P.atomicRunningCost_jointlyMeasurable b a κ).ennreal_ofReal
  have hlim := nonnegativeRunningCost_tendsto (P.continuousPathLaw h0 x) _ hm
  have hres := (P.atomicSurvival_observation_tendsto_zero_of_martingale h0 x b hb a κ hκ u hu hM).comp
    (tendsto_natCast_atTop_atTop (R := ℝ≥0))
  have hlim' := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := u x)).sub hres)
  have he (n : ℕ) := P.atomicRunningCost_finite_lintegral_of_martingale h0 x b hb a κ hκ u hM (n : ℝ≥0)
  have hfinal : Tendsto (fun n : ℕ => ∫⁻ p, (∫⁻ r in Ioc (0 : ℝ) (n : ℝ), ENNReal.ofReal
      (P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal))) ∂P.continuousPathLaw h0 x)
      atTop (𝓝 (ENNReal.ofReal (u x))) := by
    apply (show Tendsto (fun n : ℕ => ENNReal.ofReal (u x -
      ∫ p, P.atomicSurvival a κ (n : ℝ≥0) p * u (p (n : ℝ≥0)) ∂P.continuousPathLaw h0 x))
      atTop (𝓝 (ENNReal.ofReal (u x))) from by simpa only [sub_zero, Function.comp_apply] using hlim').congr'
    exact Eventually.of_forall (fun n => (he n).symm)
  exact tendsto_nhds_unique hlim hfinal

end TimeTraps.Analysis
