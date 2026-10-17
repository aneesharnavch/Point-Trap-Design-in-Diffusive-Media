module

public import TimeTraps.Probability.GraphPhysicalClockReversal
public import TimeTraps.Probability.GraphPhysicalClockAdapted

@[expose] public section

/-! The bounded Borel functional used in graph clock reversibility.
It has the actual speed at both endpoints, and the actual integrated
speed in the exponential. Reversal swaps only the endpoint tests. -/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def graphPhysicalClockPairFunctional (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (α : ℝ) (f g : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G) : ℝ :=
  Real.exp (-α * (G.physicalClock b hb T p : ℝ)) *
    (G.physicalSpeed b (p 0) * f (p 0)) * (G.physicalSpeed b (p T) * g (p T))

theorem graphPhysicalClockPairFunctional_measurable (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (α : ℝ) (f g : C(GraphRealization G, ℝ)) (T : ℝ≥0) :
    Measurable (graphPhysicalClockPairFunctional G b hb α f g T) := by
  have hc : Measurable (G.physicalClock b hb T) :=
    (G.physicalClock_measurable_past b hb T).mono ((graphContinuousNaturalFiltration G).le T) le_rfl
  have he : Measurable (fun p => Real.exp (-α * (G.physicalClock b hb T p : ℝ))) :=
    (hc.coe_nnreal_real.const_mul (-α)).exp
  have h0 : Measurable (fun p : GraphContinuousPath G => p (0 : ℝ≥0)) :=
    (continuous_eval_const 0).measurable
  have hT : Measurable (fun p : GraphContinuousPath G => p T) :=
    (continuous_eval_const T).measurable
  exact (he.mul (((G.physicalSpeed_measurable b).comp h0).mul (f.continuous.measurable.comp h0))).mul
    (((G.physicalSpeed_measurable b).comp hT).mul (g.continuous.measurable.comp hT))

theorem graphPhysicalClockPairFunctional_bound (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    {α : ℝ} (hα : 0 ≤ α) (f g : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G) :
    ‖graphPhysicalClockPairFunctional G b hb α f g T p‖ ≤
      ((G.physicalSpeedUpper b hb : ℝ) * ‖f‖) * ((G.physicalSpeedUpper b hb : ℝ) * ‖g‖) := by
  have hρ (y : GraphRealization G) : ‖G.physicalSpeed b y‖ ≤ (G.physicalSpeedUpper b hb : ℝ) := by
    rw [Real.norm_eq_abs, abs_of_nonneg ((NNReal.coe_nonneg _).trans (G.physicalSpeed_bound b hb y).1)]
    exact (G.physicalSpeed_bound b hb y).2
  have hf : ‖G.physicalSpeed b (p 0) * f (p 0)‖ ≤ (G.physicalSpeedUpper b hb : ℝ) * ‖f‖ := by
    rw [norm_mul]
    exact mul_le_mul (hρ _) (f.norm_coe_le_norm _) (norm_nonneg _) (NNReal.coe_nonneg _)
  have hg : ‖G.physicalSpeed b (p T) * g (p T)‖ ≤ (G.physicalSpeedUpper b hb : ℝ) * ‖g‖ := by
    rw [norm_mul]
    exact mul_le_mul (hρ _) (g.norm_coe_le_norm _) (norm_nonneg _) (NNReal.coe_nonneg _)
  have he : Real.exp (-α * (G.physicalClock b hb T p : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hα) (NNReal.coe_nonneg _))
  unfold graphPhysicalClockPairFunctional
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le]
  calc
    _ ≤ 1 * ‖G.physicalSpeed b (p 0) * f (p 0)‖ * ‖G.physicalSpeed b (p T) * g (p T)‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right he (norm_nonneg _)) (norm_nonneg _)
    _ ≤ _ := by
      rw [one_mul]
      exact mul_le_mul hf hg (norm_nonneg _) (mul_nonneg (NNReal.coe_nonneg _) (norm_nonneg _))

theorem graphPhysicalClockPairFunctional_reverse (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (α : ℝ) (f g : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G) :
    graphPhysicalClockPairFunctional G b hb α f g T (graphContinuousPathReverse G T p) =
      graphPhysicalClockPairFunctional G b hb α g f T p := by
  unfold graphPhysicalClockPairFunctional
  rw [G.physicalClock_reverse, graphContinuousPathReverse_zero, graphContinuousPathReverse_horizon]
  ring

theorem graphPhysicalClockPairFunctional_stop (G : MetricGraph V E) (b : ℝ) (hb : 0 < b)
    (α : ℝ) (f g : C(GraphRealization G, ℝ)) (T : ℝ≥0) (p : GraphContinuousPath G) :
    graphPhysicalClockPairFunctional G b hb α f g T (graphContinuousPathStop G T p) =
      graphPhysicalClockPairFunctional G b hb α f g T p := by
  unfold graphPhysicalClockPairFunctional
  rw [G.physicalClock_stop, graphContinuousPathStop_zero, graphContinuousPathStop_horizon]

end TimeTraps.Graph
