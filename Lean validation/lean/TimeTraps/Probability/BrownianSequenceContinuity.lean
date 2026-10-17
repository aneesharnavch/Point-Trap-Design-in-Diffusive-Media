module

public import TimeTraps.Probability.BrownianDenseContinuityRecovery
public import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

@[expose] public section

/-! Stochastic continuity from the actual fourth moments, together with
convergence of the deterministic dyadic time approximations. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem brownianSequence_tendstoInMeasure (τ : ℕ → ℝ≥0) (f : ℕ → ℕ) (j : ℕ)
    (ht : Tendsto (fun n => (τ (f n)).val) atTop (𝓝 (τ j).val)) :
    TendstoInMeasure (brownianSequenceMeasure τ) (fun n ω => ω (f n)) atTop (fun ω => ω j) := by
  apply tendstoInMeasure_iff_measureReal_dist.mpr
  intro ε hε
  have hp : Tendsto (fun n => 3 * |(τ (f n)).val - (τ j).val| ^ 2 / ε ^ 4)
      atTop (𝓝 0) := by
    simpa using (((ht.sub_const (τ j).val).abs.pow 2).const_mul 3).div_const (ε ^ 4)
  apply squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => ?_) hp
  simpa only [Real.dist_eq] using brownianSequence_increment_tail_fourth τ (f n) j hε

theorem brownianDyadicTime_floor_error (t : ℝ≥0) (n : ℕ) :
    |(brownianDyadicTime (Nat.pair n (brownianDyadicFloor t n))).val - t.val| <
      (1 / 64 : ℝ) ^ n := by
  have hp : 0 < (1 / 64 : ℝ) ^ n := by positivity
  have hx : 0 ≤ t.val * (64 : ℝ) ^ n := mul_nonneg t.coe_nonneg (by positivity)
  have h₁ := mul_le_mul_of_nonneg_right (Nat.floor_le hx) hp.le
  have h₂ := mul_lt_mul_of_pos_right (Nat.lt_floor_add_one (t.val * (64 : ℝ) ^ n)) hp
  have he : (64 : ℝ) ^ n * (1 / 64 : ℝ) ^ n = 1 := by rw [← mul_pow]; norm_num
  rw [mul_assoc, he, mul_one] at h₁ h₂
  rw [brownianDyadicTime_pair]
  change |((⌊t.val * (64 : ℝ) ^ n⌋₊ : ℝ) * (1 / 64 : ℝ) ^ n) - t.val| < _
  rw [abs_sub_comm, abs_of_nonneg (sub_nonneg.mpr h₁)]
  linarith

theorem brownianDyadicTime_floor_tendsto (t : ℝ≥0) :
    Tendsto (fun n => (brownianDyadicTime (Nat.pair n (brownianDyadicFloor t n))).val)
      atTop (𝓝 t.val) := by
  apply tendsto_iff_dist_tendsto_zero.mpr
  apply squeeze_zero (fun _ => dist_nonneg)
    (fun n => (brownianDyadicTime_floor_error t n).le)
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

end TimeTraps.Probability
