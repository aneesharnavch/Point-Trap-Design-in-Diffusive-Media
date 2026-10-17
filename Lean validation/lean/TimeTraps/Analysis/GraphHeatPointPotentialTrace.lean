module

public import TimeTraps.Analysis.GraphHeatPointPotentialEnergy
public import TimeTraps.Analysis.GraphHeatPointPotentialTraceData

@[expose] public section

/-! The original graph heat gains a point trace at the one-dimensional
short-time rate. Both its mass bound and its derivative bound are derived
from the constructed heat and the original full graph form. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.heatPointEvaluation_short_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (ht : 0 < t), t ≤ 1 →
      ∀ (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) (f : GraphL2Product P.geometry),
        (P.heatPointEvaluation t ht e x f) ^ 2 ≤
          C * (1 + 1 / Real.sqrt (t : ℝ)) * ‖f‖ ^ 2 := by
  obtain ⟨H, hH, hHb⟩ := P.heatSobolevL_h1_bound
  let B : ℝ := ∑ e, 2 / P.geometry.length e
  have hB : 0 ≤ B := Finset.sum_nonneg fun e _ =>
    div_nonneg zero_le_two (P.geometry.length_pos e).le
  have hBe (e : E) : 2 / P.geometry.length e ≤ B :=
    Finset.single_le_sum (fun d _ => div_nonneg zero_le_two (P.geometry.length_pos d).le)
      (Finset.mem_univ e)
  let C : ℝ := B + 2 + 2 * H * Real.exp 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro t ht ht1 e x f
  have htR : 0 < (t : ℝ) := ht
  have ht1R : (t : ℝ) ≤ 1 := ht1
  have hs : 0 < Real.sqrt (t : ℝ) := Real.sqrt_pos.2 htR
  have hs2 := Real.sq_sqrt htR.le
  have hdiv : Real.sqrt (t : ℝ) / (t : ℝ) = 1 / Real.sqrt (t : ℝ) := by
    apply (div_eq_div_iff htR.ne' hs.ne').2
    nlinarith
  have he : Real.exp (t : ℝ) ≤ Real.exp 1 := Real.exp_le_exp.mpr ht1R
  have hm : ‖graphSobolevSpaceStateL P.geometry (P.heatSobolevL t ht f)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [P.heatSobolevL_state]
    exact pow_le_pow_left₀ (norm_nonneg _) (P.heatSemigroup_norm_le t f) 2
  have hd : ‖P.heatSobolevL t ht f‖ ^ 2 ≤
      H * (Real.exp 1 / (t : ℝ)) * ‖f‖ ^ 2 :=
    (hHb t ht f).trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right he htR.le) hH.le) (sq_nonneg _))
  rw [P.heatPointEvaluation_apply]
  calc
    _ ≤ (2 / P.geometry.length e + 2 / Real.sqrt (t : ℝ)) *
        ‖graphSobolevSpaceStateL P.geometry (P.heatSobolevL t ht f)‖ ^ 2 +
        2 * Real.sqrt (t : ℝ) * ‖P.heatSobolevL t ht f‖ ^ 2 :=
      P.point_trace_interpolation _ e x hs
    _ ≤ (B + 2 / Real.sqrt (t : ℝ)) * ‖f‖ ^ 2 +
        2 * Real.sqrt (t : ℝ) * (H * (Real.exp 1 / (t : ℝ)) * ‖f‖ ^ 2) :=
      add_le_add (mul_le_mul (add_le_add (hBe e) le_rfl) hm (sq_nonneg _)
        (by positivity)) (mul_le_mul_of_nonneg_left hd (by positivity))
    _ = (B + (2 + 2 * H * Real.exp 1) / Real.sqrt (t : ℝ)) * ‖f‖ ^ 2 := by
      calc
        _ = (B + 2 / Real.sqrt (t : ℝ) +
            2 * H * Real.exp 1 * (Real.sqrt (t : ℝ) / (t : ℝ))) * ‖f‖ ^ 2 := by ring
        _ = _ := by rw [hdiv]; ring
    _ ≤ C * (1 + 1 / Real.sqrt (t : ℝ)) * ‖f‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      dsimp [C]
      have hq : 0 ≤ 1 / Real.sqrt (t : ℝ) := by positivity
      have hprod : 0 ≤ B * (1 / Real.sqrt (t : ℝ)) := mul_nonneg hB hq
      have hHe : 0 ≤ 2 * H * Real.exp 1 := by positivity
      simp only [div_eq_mul_inv] at hprod ⊢
      nlinarith

end TimeTraps.Analysis
