module

public import TimeTraps.Analysis.GraphShiftedContactOperatorData
public import TimeTraps.Analysis.IntervalEnergyTraceInterpolation

@[expose] public section

/-! An adjustable point trace on the original graph H1 space, separating
its ordinary L2 mass from derivative energy. This estimate includes every
closed-edge point and does not assume a heat-kernel bound. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [Fintype V] [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.edge_mass_le_state_norm_sq
    (P : GraphShiftedContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry) (e : E) :
    (∫ x in (0 : ℝ)..P.geometry.length e, P.operatorRep u e x ^ 2) ≤
      ‖graphSobolevSpaceStateL P.geometry u‖ ^ 2 := by
  change _ ≤ ‖graphSobolevStateL P.geometry u.val‖ ^ 2
  rw [graphSobolevStateL_norm_sq_integral]
  exact Finset.single_le_sum (fun d _ =>
    intervalIntegral.integral_nonneg_of_forall (P.geometry.length_pos d).le (fun _ => sq_nonneg _))
      (Finset.mem_univ e)

omit [Fintype V] [Nonempty E] in
theorem GraphShiftedContactOperatorProblem.edge_derivative_le_h1_norm_sq
    (P : GraphShiftedContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry) (e : E) :
    (∫ x in (0 : ℝ)..P.geometry.length e, deriv (P.operatorRep u e) x ^ 2) ≤ ‖u‖ ^ 2 := by
  have hm : 0 ≤ ∑ d, ∫ x in (0 : ℝ)..P.geometry.length d, P.operatorRep u d x ^ 2 :=
    Finset.sum_nonneg fun d _ => intervalIntegral.integral_nonneg_of_forall
      (P.geometry.length_pos d).le (fun _ => sq_nonneg _)
  have hd : (∫ x in (0 : ℝ)..P.geometry.length e, deriv (P.operatorRep u e) x ^ 2) ≤
      graphDerivativeSquare P.geometry (P.operatorRep u) := by
    unfold graphDerivativeSquare
    exact Finset.single_le_sum (f := fun d => ∫ x in (0 : ℝ)..P.geometry.length d,
      deriv (P.operatorRep u d) x ^ 2)
      (fun d _ => intervalIntegral.integral_nonneg_of_forall
        (P.geometry.length_pos d).le (fun x => sq_nonneg (deriv (P.operatorRep u d) x)))
      (Finset.mem_univ e)
  rw [P.operator_norm_sq]
  linarith

omit [Fintype V] in
theorem GraphShiftedContactOperatorProblem.point_trace_interpolation
    (P : GraphShiftedContactOperatorProblem V E) (u : GraphSobolevSpace P.geometry)
    (e : E) (x : Icc (0 : ℝ) (P.geometry.length e)) {ε : ℝ} (hε : 0 < ε) :
    P.operatorRep u e x ^ 2 ≤ (2 / P.geometry.length e + 2 / ε) *
      ‖graphSobolevSpaceStateL P.geometry u‖ ^ 2 + 2 * ε * ‖u‖ ^ 2 := by
  have ht := ((P.operatorRep_energy u).edge_energy e).trace_sq_interpolation
    (P.geometry.length_pos e) x.property hε
  rw [sub_zero] at ht
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_left (P.edge_mass_le_state_norm_sq u e)
      (add_nonneg (div_nonneg zero_le_two (P.geometry.length_pos e).le)
        (div_nonneg zero_le_two hε.le)))
    (mul_le_mul_of_nonneg_left (P.edge_derivative_le_h1_norm_sq u e) (by positivity)))

end TimeTraps.Analysis
