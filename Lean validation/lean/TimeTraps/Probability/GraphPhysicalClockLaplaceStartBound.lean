module

public import TimeTraps.Probability.GraphPhysicalClockLaplaceStartData

@[expose] public section

/-! A positive lower bound for the genuine Borel speed clock supplies
one exponential bound uniform in the initial point and sample path. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalClockLaplace_path_bound
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    {α : ℝ} (hα : 0 ≤ α) (g : C(GraphRealization P.geometry, ℝ))
    (r : ℝ) (p : GraphContinuousPath P.geometry) :
    ‖Real.exp (-α * (P.geometry.physicalClock b hb r.toNNReal p : ℝ)) *
      g (p r.toNNReal) * P.geometry.physicalSpeed b (p r.toNNReal)‖ ≤
      (P.geometry.physicalSpeedUpper b hb : ℝ) * ‖g‖ *
        Real.exp (-(α * (P.geometry.physicalSpeedLower b hb : ℝ)) * r) := by
  have hl : (P.geometry.physicalSpeedLower b hb : ℝ) * r ≤
      (P.geometry.physicalClock b hb r.toNNReal p : ℝ) := by
    have h := (P.geometry.physicalClock_bounds b hb r.toNNReal p).1
    have he : (P.geometry.physicalSpeedLower b hb : ℝ) * (r.toNNReal : ℝ) ≤
        (P.geometry.physicalClock b hb r.toNNReal p : ℝ) := by exact_mod_cast h
    exact (mul_le_mul_of_nonneg_left (Real.le_coe_toNNReal r)
      (P.geometry.physicalSpeedLower b hb).coe_nonneg).trans he
  have he : Real.exp (-α * (P.geometry.physicalClock b hb r.toNNReal p : ℝ)) ≤
      Real.exp (-(α * (P.geometry.physicalSpeedLower b hb : ℝ)) * r) := by
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hl hα]
  have hs := P.geometry.physicalSpeed_bound b hb (p r.toNNReal)
  have hs0 : 0 ≤ P.geometry.physicalSpeed b (p r.toNNReal) :=
    (P.geometry.physicalSpeedLower b hb).coe_nonneg.trans hs.1
  rw [norm_mul, norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le,
    Real.norm_of_nonneg hs0]
  have hprod := mul_le_mul he (g.norm_coe_le_norm (p r.toNNReal))
    (norm_nonneg _) (Real.exp_pos _).le
  have hfull := mul_le_mul hprod hs.2 hs0
    (mul_nonneg (Real.exp_pos _).le (norm_nonneg g))
  exact hfull.trans_eq (by ring)

theorem GraphShiftedContactOperatorProblem.physicalClockLaplaceIntegrand_bound
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) {α : ℝ} (hα : 0 ≤ α)
    (g : C(GraphRealization P.geometry, ℝ)) (r : ℝ)
    (x : GraphRealization P.geometry) :
    ‖P.physicalClockLaplaceIntegrand h0 b hb α g r x‖ ≤
      (P.geometry.physicalSpeedUpper b hb : ℝ) * ‖g‖ *
        Real.exp (-(α * (P.geometry.physicalSpeedLower b hb : ℝ)) * r) := by
  let inst := P.continuousPathLaw_probability h0 x
  have h := norm_integral_le_of_norm_le_const (μ := P.continuousPathLaw h0 x)
    (Eventually.of_forall (P.physicalClockLaplace_path_bound b hb hα g r))
  simpa only [physicalClockLaplaceIntegrand, probReal_univ, mul_one] using h

end TimeTraps.Analysis
