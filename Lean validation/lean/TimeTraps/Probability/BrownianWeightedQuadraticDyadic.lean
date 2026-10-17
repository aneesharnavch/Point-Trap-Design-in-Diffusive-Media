module

public import TimeTraps.Probability.BrownianWeightedQuadraticBound
public import TimeTraps.Probability.BrownianQuadraticVariation

@[expose] public section

/-! Weighted compensated quadratic variation on dyadic partitions has
mean zero and squared L² norm at most 2 M² T² / 2ⁿ. The entire triangular
array of weights may vary with n while retaining the same bound M. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem brownianDyadicGrid_squared_gaps (T : ℝ≥0) (n : ℕ) :
    (∑ i : Fin (2 ^ n), ((brownianDyadicGrid T n i.succ).val -
      (brownianDyadicGrid T n i.castSucc).val) ^ 2) = T.val ^ 2 / (2 : ℝ) ^ n := by
  calc
    _ = ∑ _ : Fin (2 ^ n), (T.val / (2 : ℝ) ^ n) ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      rw [← sq_abs ((brownianDyadicGrid T n i.succ).val - (brownianDyadicGrid T n i.castSucc).val),
        brownianDyadicGrid_gap]
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        Nat.cast_pow, Nat.cast_ofNat]
      field_simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianWeightedDyadicQuadratic (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ)
    (ξ : Fin (2 ^ n) → Ω → ℝ) : Ω → ℝ :=
  brownianWeightedQuadraticSum B (brownianDyadicGrid T n) ξ

theorem brownianWeightedDyadicQuadratic_zero (B : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (ξ : Fin (2 ^ n) → Ω → ℝ) (ω : Ω) : brownianWeightedDyadicQuadratic B 0 n ξ ω = 0 := by
  simp [brownianWeightedDyadicQuadratic, brownianWeightedQuadraticSum,
    brownianCompensatedSquareIncrement, brownianDyadicGrid]

theorem brownianWeightedDyadicQuadratic_mean (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) (ξ : Fin (2 ^ n) → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (brownianDyadicGrid T n i.castSucc)] (ξ i))
    (M : ℝ≥0) (hb : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ M.val) :
    (∫ ω, brownianWeightedDyadicQuadratic B T n ξ ω ∂P) = 0 :=
  brownianBoundedQuadraticSum_mean hB hBm _ (brownianDyadicGrid_monotone T n) ξ hξ M hb

theorem brownianWeightedDyadicQuadratic_secondMoment_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) (ξ : Fin (2 ^ n) → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (brownianDyadicGrid T n i.castSucc)] (ξ i))
    (M : ℝ≥0) (hb : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ M.val) :
    (∫ ω, brownianWeightedDyadicQuadratic B T n ξ ω ^ 2 ∂P) ≤
      2 * M.val ^ 2 * T.val ^ 2 / (2 : ℝ) ^ n := by
  have h := brownianBoundedQuadraticSum_secondMoment_le hB hBm _ (brownianDyadicGrid_monotone T n) ξ hξ M hb
  rw [brownianDyadicGrid_squared_gaps] at h
  exact h.trans_eq (by ring)

noncomputable def brownianWeightedDyadicQuadraticL2 (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (ξ : Fin (2 ^ n) → Ω → ℝ)
    (hSum : MemLp (brownianWeightedDyadicQuadratic B T n ξ) 2 P) : Lp ℝ 2 P :=
  brownianWeightedQuadraticSumL2 B (brownianDyadicGrid T n) ξ hSum

theorem brownianWeightedDyadicQuadratic_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) (ξ : Fin (2 ^ n) → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (brownianDyadicGrid T n i.castSucc)] (ξ i))
    (M : ℝ≥0) (hb : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ M.val) :
    MemLp (brownianWeightedDyadicQuadratic B T n ξ) 2 P :=
  brownianBoundedQuadraticSum_memLp hB hBm _ (brownianDyadicGrid_monotone T n) ξ hξ M hb

theorem brownianWeightedDyadicQuadraticL2_coe (B : ℝ≥0 → Ω → ℝ)
    (T : ℝ≥0) (n : ℕ) (ξ : Fin (2 ^ n) → Ω → ℝ)
    (hSum : MemLp (brownianWeightedDyadicQuadratic B T n ξ) 2 P) :
    brownianWeightedDyadicQuadraticL2 B T n ξ hSum =ᵐ[P] brownianWeightedDyadicQuadratic B T n ξ :=
  brownianWeightedQuadraticSumL2_coe B _ ξ hSum

theorem brownianWeightedDyadicQuadraticL2_norm_sq_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) (ξ : Fin (2 ^ n) → Ω → ℝ)
    (hξ : ∀ i, StronglyMeasurable[brownianNaturalFiltration B hBm (brownianDyadicGrid T n i.castSucc)] (ξ i))
    (M : ℝ≥0) (hb : ∀ i, ∀ᵐ ω ∂P, |ξ i ω| ≤ M.val)
    (hSum : MemLp (brownianWeightedDyadicQuadratic B T n ξ) 2 P) :
    ‖brownianWeightedDyadicQuadraticL2 B T n ξ hSum‖ ^ 2 ≤
      2 * M.val ^ 2 * T.val ^ 2 / (2 : ℝ) ^ n := by
  have h := brownianBoundedQuadraticSumL2_norm_sq_le hB hBm _ (brownianDyadicGrid_monotone T n) ξ hξ M hb hSum
  rw [brownianDyadicGrid_squared_gaps] at h
  exact h.trans_eq (by ring)

theorem brownianWeightedDyadicQuadraticL2_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) (ξ : (n : ℕ) → Fin (2 ^ n) → Ω → ℝ)
    (hξ : ∀ n i, StronglyMeasurable[brownianNaturalFiltration B hBm (brownianDyadicGrid T n i.castSucc)] (ξ n i))
    (M : ℝ≥0) (hb : ∀ n i, ∀ᵐ ω ∂P, |ξ n i ω| ≤ M.val)
    (hSum : ∀ n, MemLp (brownianWeightedDyadicQuadratic B T n (ξ n)) 2 P) :
    Tendsto (fun n => brownianWeightedDyadicQuadraticL2 B T n (ξ n) (hSum n))
      atTop (𝓝 (0 : Lp ℝ 2 P)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero]
  have hrate : Tendsto (fun n => 2 * M.val ^ 2 * T.val ^ 2 / (2 : ℝ) ^ n) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, inv_pow, one_mul, mul_zero] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (2 * M.val ^ 2 * T.val ^ 2)
  have hs := squeeze_zero (fun n => sq_nonneg
    ‖brownianWeightedDyadicQuadraticL2 B T n (ξ n) (hSum n)‖)
    (fun n => brownianWeightedDyadicQuadraticL2_norm_sq_le hB hBm T n (ξ n) (hξ n) M (hb n) (hSum n)) hrate
  have hr := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hr

end TimeTraps.Probability
