module

public import TimeTraps.Probability.BrownianQuadraticVariationMoments

@[expose] public section

/-! The actual squared-increment sum on the uniform dyadic partition of
`[0,T]` has expectation `T` and centered second moment `2 T² / 2ⁿ`.
All formulas are exact and include `T = 0`. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianDyadicGrid (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n + 1)) : ℝ≥0 :=
  i.val * T / (2 : ℝ≥0) ^ n

theorem brownianDyadicGrid_monotone (T : ℝ≥0) (n : ℕ) : Monotone (brownianDyadicGrid T n) := by
  intro i j hij
  unfold brownianDyadicGrid
  gcongr
  exact hij

theorem brownianDyadicGrid_gap (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) :
    |(brownianDyadicGrid T n i.succ).val - (brownianDyadicGrid T n i.castSucc).val| =
      T.val / (2 : ℝ) ^ n := by
  change |((i.val + 1 : ℕ) : ℝ) * T.val / (2 : ℝ) ^ n -
    (i.val : ℝ) * T.val / (2 : ℝ) ^ n| = _
  rw [Nat.cast_add, Nat.cast_one]
  rw [show ((i.val : ℝ) + 1) * T.val / (2 : ℝ) ^ n -
    (i.val : ℝ) * T.val / (2 : ℝ) ^ n = T.val / (2 : ℝ) ^ n by ring]
  exact abs_of_nonneg (div_nonneg T.coe_nonneg (by positivity))

noncomputable def brownianDyadicQV (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) : Ω → ℝ :=
  brownianPartitionQV B (brownianDyadicGrid T n)

theorem brownianDyadicQV_mean (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, brownianDyadicQV B T n ω ∂P) = T.val := by
  rw [brownianDyadicQV, brownianPartitionQV_mean hB]
  simp only [brownianDyadicGrid_gap, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem brownianDyadicQV_variance (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    Var[brownianDyadicQV B T n; P] = 2 * T.val ^ 2 / (2 : ℝ) ^ n := by
  rw [brownianDyadicQV, brownianPartitionQV_variance hB _ (brownianDyadicGrid_monotone T n)]
  simp only [brownianDyadicGrid_gap, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

theorem brownianDyadicQV_l2_error (hB : IsPreBrownianReal B P) (T : ℝ≥0) (n : ℕ) :
    (∫ ω, (brownianDyadicQV B T n ω - T.val) ^ 2 ∂P) = 2 * T.val ^ 2 / (2 : ℝ) ^ n := by
  calc
    _ = Var[brownianDyadicQV B T n; P] := by
      have hv := variance_eq_integral (X := brownianDyadicQV B T n)
        (brownianPartitionQV_memLp hB (brownianDyadicGrid T n)).aemeasurable
      rw [brownianDyadicQV_mean hB T n] at hv
      exact hv.symm
    _ = _ := brownianDyadicQV_variance hB T n

theorem brownianDyadicQV_l2_converges (hB : IsPreBrownianReal B P) (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (brownianDyadicQV B T n ω - T.val) ^ 2 ∂P) atTop (𝓝 0) := by
  simp only [brownianDyadicQV_l2_error hB T]
  simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
    (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * T.val ^ 2)

theorem brownianDyadicPath_qv_mean (T : ℝ≥0) (n : ℕ) :
    (∫ ω, brownianDyadicQV brownianDyadicPath T n ω ∂brownianDyadicMeasure) = T.val :=
  brownianDyadicQV_mean brownianDyadicPath_isPreBrownianReal T n

theorem brownianDyadicPath_qv_l2_error (T : ℝ≥0) (n : ℕ) :
    (∫ ω, (brownianDyadicQV brownianDyadicPath T n ω - T.val) ^ 2 ∂brownianDyadicMeasure) =
      2 * T.val ^ 2 / (2 : ℝ) ^ n :=
  brownianDyadicQV_l2_error brownianDyadicPath_isPreBrownianReal T n

theorem brownianDyadicPath_qv_l2_converges (T : ℝ≥0) :
    Tendsto (fun n => ∫ ω, (brownianDyadicQV brownianDyadicPath T n ω - T.val) ^ 2
      ∂brownianDyadicMeasure) atTop (𝓝 0) :=
  brownianDyadicQV_l2_converges brownianDyadicPath_isPreBrownianReal T

end TimeTraps.Probability
