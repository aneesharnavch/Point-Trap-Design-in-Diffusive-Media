module

public import TimeTraps.Analysis.GraphHeatPointPotentialRealized

@[expose] public section

/-! Contraction after a fixed positive time extends the derived point
kernel bound to all times. Consequently every finite-time point potential
is an actual integrable quantity, with a uniform spatial bound. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph InnerProductSpace
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.heatKernelVector_norm_antitone
    (P : GraphShiftedContactOperatorProblem V E) (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t)
    (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) :
    ‖P.heatKernelVector t (hs.trans_le hst) e x‖ ≤ ‖P.heatKernelVector s hs e x‖ := by
  have he : P.heatKernelVector t (hs.trans_le hst) e x =
      P.heatSemigroup (t - s) (P.heatKernelVector s hs e x) := by
    simpa only [add_tsub_cancel_of_le hst] using P.heatKernelVector_add s hs (t - s) e x
  rw [he]
  exact P.heatSemigroup_norm_le _ _

theorem GraphShiftedContactOperatorProblem.heatKernel_global_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (ht : 0 < t)
      (e d : E) (x : Icc (0 : ℝ) (P.geometry.length e))
        (y : Icc (0 : ℝ) (P.geometry.length d)),
        0 ≤ P.heatKernel t ht e x d y ∧
          P.heatKernel t ht e x d y ≤ C * (1 + 1 / Real.sqrt (t : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := P.heatKernel_short_bound
  obtain ⟨D, hD, hv⟩ := P.heatKernelVector_short_bound
  let K : ℝ := D * (1 + 1 / Real.sqrt (1 / 2 : ℝ))
  have hK : 0 < K := by dsimp [K]; positivity
  refine ⟨C + K, by positivity, ?_⟩
  intro t ht e d x y
  refine ⟨P.heatKernel_nonneg t ht e d x y, ?_⟩
  by_cases ht1 : t ≤ 1
  · exact (hb t ht ht1 e d x y).2.trans
      (mul_le_mul_of_nonneg_right (by linarith : C ≤ C + K) (by positivity))
  · have hh : (1 / 2 : ℝ≥0) ≤ t / 2 := div_le_div_of_nonneg_right (le_of_not_ge ht1) (by norm_num)
    have hx : ‖P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) e x‖ ^ 2 ≤ K := by
      calc
        _ ≤ ‖P.heatKernelVector (1 / 2) (by norm_num) e x‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _)
            (P.heatKernelVector_norm_antitone (1 / 2) (t / 2) (by norm_num) hh e x) 2
        _ ≤ K := by
          simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
            (hv (1 / 2) (by norm_num) (by norm_num) e x)
    have hy : ‖P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) d y‖ ^ 2 ≤ K := by
      calc
        _ ≤ ‖P.heatKernelVector (1 / 2) (by norm_num) d y‖ ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _)
            (P.heatKernelVector_norm_antitone (1 / 2) (t / 2) (by norm_num) hh d y) 2
        _ ≤ K := by
          simpa only [NNReal.coe_div, NNReal.coe_one, NNReal.coe_ofNat] using
            (hv (1 / 2) (by norm_num) (by norm_num) d y)
    have hp : P.heatKernel t ht e x d y ≤ K := by
      rw [P.heatKernel_eq_inner]
      have hi := real_inner_le_norm (P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) e x)
        (P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) d y)
      nlinarith [sq_nonneg (‖P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) e x‖ -
        ‖P.heatKernelVector (t / 2) (div_pos ht (by norm_num)) d y‖)]
    apply hp.trans
    have hq : 0 ≤ (C + K) * (1 / Real.sqrt (t : ℝ)) := by positivity
    nlinarith

theorem GraphShiftedContactOperatorProblem.realizedHeatKernel_global_bound
    (P : GraphShiftedContactOperatorProblem V E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (ht : 0 < t) (x y : GraphRealization P.geometry),
      0 ≤ P.realizedHeatKernel t ht x y ∧
        P.realizedHeatKernel t ht x y ≤ C * (1 + 1 / Real.sqrt (t : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := P.heatKernel_global_bound
  refine ⟨C, hC, ?_⟩
  intro t ht x y
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  obtain ⟨d, v, rfl⟩ := P.geometry.edgePoint_surjective y
  rw [P.realizedHeatKernel_edge]
  exact hb t ht e d u v

end TimeTraps.Analysis
