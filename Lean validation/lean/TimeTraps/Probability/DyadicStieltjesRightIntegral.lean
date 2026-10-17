module

public import TimeTraps.Probability.DyadicStieltjesIntegral
public import TimeTraps.Probability.BrownianItoC2Remainder

@[expose] public section

/-! Right-endpoint dyadic Stieltjes sums have the same actual integral
limit as left-endpoint sums for continuous weights. Monotonicity bounds
the error by the compact variation times the modulus of the weight;
the Stieltjes integrator itself need not be continuous. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def dyadicStieltjesRightSum (K : StieltjesFunction ℝ)
    (g : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i : Fin (2 ^ n),
    (K (brownianDyadicGrid T n i.succ).val - K (brownianDyadicGrid T n i.castSucc).val) *
      g (brownianDyadicGrid T n i.succ)

theorem dyadicStieltjesRightSum_sub_left_tendsto (K : StieltjesFunction ℝ)
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    Tendsto (fun n => dyadicStieltjesRightSum K g T n - dyadicStieltjesSum K g T n)
      atTop (𝓝 0) := by
  let V : ℝ := K T.val - K 0
  have hV : 0 ≤ V := sub_nonneg.mpr (K.mono T.coe_nonneg)
  have hinc (n : ℕ) (i : Fin (2 ^ n)) :
      0 ≤ K (brownianDyadicGrid T n i.succ).val -
        K (brownianDyadicGrid T n i.castSucc).val :=
    sub_nonneg.mpr (K.mono (brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i)))
  have htel (n : ℕ) : (∑ i : Fin (2 ^ n),
      (K (brownianDyadicGrid T n i.succ).val -
        K (brownianDyadicGrid T n i.castSucc).val)) = V := by
    have he := finite_sum_increments
      (fun i : Fin (2 ^ n + 1) => K (brownianDyadicGrid T n i).val)
    calc
      _ = K T.val - K (0 : ℝ≥0).val := by
        simpa only [brownianDyadicGrid_last, brownianDyadicGrid_zero] using he
      _ = V := rfl
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (V + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  filter_upwards [dyadicPath_increments_eventually_small g T hg.continuousOn hη] with n hn
  have he : dyadicStieltjesRightSum K g T n - dyadicStieltjesSum K g T n =
      ∑ i : Fin (2 ^ n),
        (K (brownianDyadicGrid T n i.succ).val - K (brownianDyadicGrid T n i.castSucc).val) *
          (g (brownianDyadicGrid T n i.succ) - g (brownianDyadicGrid T n i.castSucc)) := by
    simp only [dyadicStieltjesRightSum, dyadicStieltjesSum, mul_sub, Finset.sum_sub_distrib]
  rw [Real.dist_eq, sub_zero, he]
  calc
    _ ≤ ∑ i : Fin (2 ^ n),
        |(K (brownianDyadicGrid T n i.succ).val - K (brownianDyadicGrid T n i.castSucc).val) *
          (g (brownianDyadicGrid T n i.succ) - g (brownianDyadicGrid T n i.castSucc))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (2 ^ n),
        (K (brownianDyadicGrid T n i.succ).val - K (brownianDyadicGrid T n i.castSucc).val) * η := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_of_nonneg (hinc n i)]
      exact mul_le_mul_of_nonneg_left (hn i).le (hinc n i)
    _ = V * η := by rw [← Finset.sum_mul, htel]
    _ < ε := by
      have he : η * (V + 1) = ε := div_mul_cancel₀ ε (by linarith : V + 1 ≠ 0)
      nlinarith

theorem dyadicStieltjesRightSum_tendsto (K : StieltjesFunction ℝ)
    (g : ℝ≥0 → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    Tendsto (dyadicStieltjesRightSum K g T) atTop
      (𝓝 (∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal ∂K.measure)) := by
  have h := (dyadicStieltjesRightSum_sub_left_tendsto K g hg T).add
    (dyadicStieltjesSum_tendsto K g hg T)
  simpa only [sub_add_cancel, zero_add] using h

theorem dyadicStieltjes_product_identity (K : StieltjesFunction ℝ)
    (g : ℝ≥0 → ℝ) (c : ℝ) (T : ℝ≥0) (n : ℕ) :
    (c - K T.val) * g T - (c - K 0) * g 0 =
      (∑ i : Fin (2 ^ n), (c - K (brownianDyadicGrid T n i.castSucc).val) *
        (g (brownianDyadicGrid T n i.succ) - g (brownianDyadicGrid T n i.castSucc))) -
      dyadicStieltjesRightSum K g T n := by
  have he := finite_sum_increments
    (fun i : Fin (2 ^ n + 1) => (c - K (brownianDyadicGrid T n i).val) *
      g (brownianDyadicGrid T n i))
  have ht : (∑ i : Fin (2 ^ n),
      ((c - K (brownianDyadicGrid T n i.succ).val) * g (brownianDyadicGrid T n i.succ) -
        (c - K (brownianDyadicGrid T n i.castSucc).val) * g (brownianDyadicGrid T n i.castSucc))) =
      (c - K T.val) * g T - (c - K 0) * g 0 := by
    calc
      _ = (c - K T.val) * g T - (c - K (0 : ℝ≥0).val) * g 0 := by
        simpa only [brownianDyadicGrid_last, brownianDyadicGrid_zero] using he
      _ = _ := rfl
  rw [← ht, dyadicStieltjesRightSum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

end TimeTraps.Probability
