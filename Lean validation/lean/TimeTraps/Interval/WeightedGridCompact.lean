module

public import TimeTraps.Interval.WeightedGridDistance
public import Mathlib.Topology.MetricSpace.Lipschitz
public import Mathlib.Topology.MetricSpace.Pseudo.Pi

@[expose] public section

/-! The actual nearest-grid integral is Lipschitz on the closed grid space
and attains its minimum. Repeated nodes are allowed at this compactness
stage; strictness and physical reconstruction are separate statements. -/

namespace TimeTraps.Interval

open Set MeasureTheory

variable {n : ℕ}

noncomputable def ClosedPartition.gridCost (Q : ClosedPartition n) (W : CellWeight) : ℝ :=
  ∫ x in (0 : ℝ)..1, W.value x * gridDistance Q.point x ^ 2

theorem ClosedPartition.gridCost_integrable (Q : ClosedPartition n) (W : CellWeight) :
    IntervalIntegrable (fun x => W.value x * gridDistance Q.point x ^ 2) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  intro x hx
  exact (W.continuous x hx).mul
    ((gridDistance_continuous Q.point).continuousAt.continuousWithinAt.pow 2)

theorem ClosedPartition.gridCost_nonneg (Q : ClosedPartition n) (W : CellWeight) :
    0 ≤ Q.gridCost W :=
  intervalIntegral.integral_nonneg zero_le_one
    (fun x hx => mul_nonneg (W.positive x hx).le (sq_nonneg _))

theorem ClosedPartition.gridCost_perturbation (Q R : ClosedPartition n) (W : CellWeight)
    {δ : ℝ} (h : ∀ i, |Q.point i - R.point i| ≤ δ) :
    |Q.gridCost W - R.gridCost W| ≤ 2 * δ * ∫ x in (0 : ℝ)..1, W.value x := by
  have hi : IntervalIntegrable W.value volume 0 1 := by
    apply ContinuousOn.intervalIntegrable
    simpa only [uIcc_of_le zero_le_one] using W.continuous
  have hb := intervalIntegral.norm_integral_le_of_norm_le (f := fun x =>
      W.value x * gridDistance Q.point x ^ 2 - W.value x * gridDistance R.point x ^ 2)
    zero_le_one (Filter.Eventually.of_forall (fun x hx => ?_)) (hi.const_mul (2 * δ))
  · rw [intervalIntegral.integral_sub (Q.gridCost_integrable W) (R.gridCost_integrable W),
      intervalIntegral.integral_const_mul, Real.norm_eq_abs] at hb
    exact hb
  · have hx' : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg (W.positive x hx').le]
    calc
      _ ≤ W.value x * (2 * δ) := mul_le_mul_of_nonneg_left
        (Q.gridDistance_square_lipschitz R h hx') (W.positive x hx').le
      _ = _ := by ring

theorem ClosedPartition.gridCost_lipschitz (W : CellWeight) :
    LipschitzWith ⟨2 * ∫ x in (0 : ℝ)..1, W.value x,
      mul_nonneg (by norm_num) (intervalIntegral.integral_nonneg zero_le_one
        (fun x hx => (W.positive x hx).le))⟩
      (fun Q : ClosedPartition n => Q.gridCost W) := by
  apply LipschitzWith.of_dist_le_mul
  intro Q R
  have h (i : Fin (n + 1)) : |Q.point i - R.point i| ≤ dist Q R := by
    exact_mod_cast dist_le_pi_dist Q.val R.val i
  have hb := Q.gridCost_perturbation R W h
  change |Q.gridCost W - R.gridCost W| ≤
    (2 * ∫ x in (0 : ℝ)..1, W.value x) * dist Q R
  simpa only [Real.dist_eq, mul_assoc, mul_left_comm, mul_comm] using hb

theorem ClosedPartition.gridCost_continuous (W : CellWeight) :
    Continuous (fun Q : ClosedPartition n => Q.gridCost W) :=
  (ClosedPartition.gridCost_lipschitz W).continuous

theorem ClosedPartition.grid_minimum_exists (W : CellWeight) (hn : 0 < n) :
    ∃ Q : ClosedPartition n, ∀ R : ClosedPartition n, Q.gridCost W ≤ R.gridCost W := by
  obtain ⟨Q, _, hQ⟩ := isCompact_univ.exists_isMinOn
    (show (Set.univ : Set (ClosedPartition n)).Nonempty from
      ⟨(StrictPartition.uniform n hn).closed, mem_univ _⟩)
    (ClosedPartition.gridCost_continuous W).continuousOn
  exact ⟨Q, fun R => hQ (mem_univ R)⟩

theorem ClosedPartition.grid_minimum_isLeast (W : CellWeight) (hn : 0 < n) :
    ∃ Q : ClosedPartition n,
      IsLeast (range (fun R : ClosedPartition n => R.gridCost W)) (Q.gridCost W) := by
  obtain ⟨Q, hQ⟩ := ClosedPartition.grid_minimum_exists W hn
  refine ⟨Q, ⟨Q, rfl⟩, ?_⟩
  rintro M ⟨R, rfl⟩
  exact hQ R

end TimeTraps.Interval
