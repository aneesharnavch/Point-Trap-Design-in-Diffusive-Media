module

public import TimeTraps.Probability.BrownianQuadraticVariationAlmostSure
public import TimeTraps.Probability.ContinuousMonotoneQuadraticVariation

@[expose] public section

/-! Stopping every node of the dyadic grid at `s` gives an actual finite
partition of `[0,min s T]`, with repeated nodes permitted. Its quadratic
variation has the exact mean `min s T` and a summable squared-error bound
uniform in the stopping time. No sample-path regularity is assumed here. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianStoppedDyadicGrid (T s : ℝ≥0) (n : ℕ)
    (i : Fin (2 ^ n + 1)) : ℝ≥0 := min s (brownianDyadicGrid T n i)

theorem brownianStoppedDyadicGrid_monotone (T s : ℝ≥0) (n : ℕ) :
    Monotone (brownianStoppedDyadicGrid T s n) :=
  fun _ _ hij => min_le_min_left s (brownianDyadicGrid_monotone T n hij)

theorem brownianStoppedDyadicGrid_zero (T s : ℝ≥0) (n : ℕ) :
    brownianStoppedDyadicGrid T s n 0 = 0 := by
  simp only [brownianStoppedDyadicGrid, brownianDyadicGrid_zero, min_eq_right (show 0 ≤ s from zero_le)]

theorem brownianStoppedDyadicGrid_last (T s : ℝ≥0) (n : ℕ) :
    brownianStoppedDyadicGrid T s n (Fin.last (2 ^ n)) = min s T := by
  simp only [brownianStoppedDyadicGrid, brownianDyadicGrid_last]

theorem brownianStoppedDyadicGrid_gap_le (T s : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) :
    |(brownianStoppedDyadicGrid T s n i.succ).val -
      (brownianStoppedDyadicGrid T s n i.castSucc).val| ≤ T.val / (2 : ℝ) ^ n := by
  calc
    _ = |min s.val (brownianDyadicGrid T n i.succ).val -
        min s.val (brownianDyadicGrid T n i.castSucc).val| := rfl
    _ ≤ max |s.val - s.val| |(brownianDyadicGrid T n i.succ).val -
        (brownianDyadicGrid T n i.castSucc).val| := abs_min_sub_min_le_max _ _ _ _
    _ = |(brownianDyadicGrid T n i.succ).val -
        (brownianDyadicGrid T n i.castSucc).val| := by
      simp only [sub_self, abs_zero]
      exact max_eq_right (abs_nonneg ((brownianDyadicGrid T n i.succ).val -
        (brownianDyadicGrid T n i.castSucc).val))
    _ = _ := brownianDyadicGrid_gap T n i

noncomputable def brownianStoppedDyadicQV (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (s : ℝ≥0) : Ω → ℝ :=
  brownianPartitionQV B (brownianStoppedDyadicGrid T s n)

theorem brownianStoppedDyadicQV_mean (hB : IsPreBrownianReal B P) (T s : ℝ≥0) (n : ℕ) :
    (∫ ω, brownianStoppedDyadicQV B T n s ω ∂P) = (min s T).val := by
  rw [brownianStoppedDyadicQV, brownianPartitionQV_mean hB]
  have he (i : Fin (2 ^ n)) :
      |(brownianStoppedDyadicGrid T s n i.succ).val -
        (brownianStoppedDyadicGrid T s n i.castSucc).val| =
      (brownianStoppedDyadicGrid T s n i.succ).val -
        (brownianStoppedDyadicGrid T s n i.castSucc).val :=
    abs_of_nonneg (sub_nonneg.mpr
      (brownianStoppedDyadicGrid_monotone T s n (Fin.castSucc_le_succ i)))
  simp only [he]
  calc
    _ = (brownianStoppedDyadicGrid T s n (Fin.last (2 ^ n))).val -
        (brownianStoppedDyadicGrid T s n 0).val :=
      finite_sum_increments (fun i => (brownianStoppedDyadicGrid T s n i).val)
    _ = (min s T).val - (0 : ℝ≥0).val :=
      congrArg₂ (fun a b : ℝ≥0 => a.val - b.val)
        (brownianStoppedDyadicGrid_last T s n) (brownianStoppedDyadicGrid_zero T s n)
    _ = _ := sub_zero _

theorem brownianStoppedDyadicQV_variance_le (hB : IsPreBrownianReal B P)
    (T s : ℝ≥0) (n : ℕ) :
    Var[brownianStoppedDyadicQV B T n s; P] ≤ 2 * T.val ^ 2 / (2 : ℝ) ^ n := by
  rw [brownianStoppedDyadicQV, brownianPartitionQV_variance hB _
    (brownianStoppedDyadicGrid_monotone T s n)]
  have hm : Monotone (fun i => (brownianStoppedDyadicGrid T s n i).val) :=
    brownianStoppedDyadicGrid_monotone T s n
  have hb := finiteQuadraticVariation_monotone_bound
    (fun i => (brownianStoppedDyadicGrid T s n i).val) hm
    (fun i => (le_abs_self _).trans (brownianStoppedDyadicGrid_gap_le T s n i))
  have hend : (brownianStoppedDyadicGrid T s n (Fin.last (2 ^ n))).val -
      (brownianStoppedDyadicGrid T s n 0).val = (min s T).val := by
    calc
      _ = (min s T).val - (0 : ℝ≥0).val :=
        congrArg₂ (fun a b : ℝ≥0 => a.val - b.val)
          (brownianStoppedDyadicGrid_last T s n) (brownianStoppedDyadicGrid_zero T s n)
      _ = _ := sub_zero _
  have hb' := hb.trans_eq (congrArg (fun r : ℝ => T.val / (2 : ℝ) ^ n * r) hend)
  calc
    _ = 2 * finiteQuadraticVariation (fun i => (brownianStoppedDyadicGrid T s n i).val) := by
      simp only [finiteQuadraticVariation, Finset.mul_sum, sq_abs]
    _ ≤ 2 * (T.val / (2 : ℝ) ^ n * (min s T).val) := mul_le_mul_of_nonneg_left hb' (by norm_num)
    _ ≤ 2 * (T.val / (2 : ℝ) ^ n * T.val) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (show (min s T).val ≤ T.val from min_le_right s T)
          (div_nonneg T.coe_nonneg (by positivity))) (by norm_num)
    _ = _ := by ring

theorem brownianStoppedDyadicQV_l2_error_le (hB : IsPreBrownianReal B P)
    (T s : ℝ≥0) (n : ℕ) :
    (∫ ω, (brownianStoppedDyadicQV B T n s ω - (min s T).val) ^ 2 ∂P) ≤
      2 * T.val ^ 2 / (2 : ℝ) ^ n := by
  calc
    _ = Var[brownianStoppedDyadicQV B T n s; P] := by
      have hv := variance_eq_integral (X := brownianStoppedDyadicQV B T n s)
        (brownianPartitionQV_memLp hB (brownianStoppedDyadicGrid T s n)).aemeasurable
      rw [brownianStoppedDyadicQV_mean hB T s n] at hv
      exact hv.symm
    _ ≤ _ := brownianStoppedDyadicQV_variance_le hB T s n

end TimeTraps.Probability
