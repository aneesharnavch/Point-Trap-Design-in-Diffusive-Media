module

public import TimeTraps.Probability.DyadicWeightedIncrement
public import TimeTraps.Probability.DyadicStieltjesRightIntegral

@[expose] public section

/-! Finite signed path decompositions pass to the actual weighted
increment sums. The same definition agrees with Stieltjes sums and
has the exact left/right product identity for weights c-K. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal Topology

theorem dyadicWeightedIncrement_decomposition {ι : Type*} [Fintype ι]
    (H q J b : ℝ≥0 → ℝ) (c : ι → ℝ) (r : ι → ℝ≥0 → ℝ) {T : ℝ≥0}
    (hq : ∀ t ∈ Icc 0 T, q t - q 0 = J t + b t + ∑ j, c j * r j t) (n : ℕ) :
    dyadicWeightedIncrement H q T n = dyadicWeightedIncrement H J T n +
      dyadicWeightedIncrement H b T n + ∑ j, c j * dyadicWeightedIncrement H (r j) T n := by
  calc
    _ = dyadicWeightedIncrement H (fun t => J t + b t + ∑ j, c j * r j t) T n :=
      dyadicWeightedIncrement_congr_of_sub_const H q _ (q 0) hq n
    _ = _ := by
      simp only [dyadicWeightedIncrement_add, dyadicWeightedIncrement_sum,
        dyadicWeightedIncrement_const_mul]

theorem dyadicWeightedIncrement_boundary_decomposition {ι : Type*} [Fintype ι]
    (H q J b lower upper : ℝ≥0 → ℝ) (c : ι → ℝ) (r : ι → ℝ≥0 → ℝ)
    (cl cu : ℝ) {T : ℝ≥0}
    (hq : ∀ t ∈ Icc 0 T, q t - q 0 =
      J t + b t + (∑ j, c j * r j t) + cl * lower t - cu * upper t) (n : ℕ) :
    dyadicWeightedIncrement H q T n = dyadicWeightedIncrement H J T n +
      dyadicWeightedIncrement H b T n + (∑ j, c j * dyadicWeightedIncrement H (r j) T n) +
      cl * dyadicWeightedIncrement H lower T n - cu * dyadicWeightedIncrement H upper T n := by
  calc
    _ = dyadicWeightedIncrement H (fun t =>
        J t + b t + (∑ j, c j * r j t) + cl * lower t - cu * upper t) T n :=
      dyadicWeightedIncrement_congr_of_sub_const H q _ (q 0) hq n
    _ = _ := by
      simp only [dyadicWeightedIncrement_add, dyadicWeightedIncrement_sub,
        dyadicWeightedIncrement_sum, dyadicWeightedIncrement_const_mul]

theorem dyadicWeightedIncrement_stieltjes (K : StieltjesFunction ℝ)
    (H : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    dyadicWeightedIncrement H (fun t => K t.val) T n = dyadicStieltjesSum K H T n := by
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

theorem dyadicWeightedIncrement_stieltjes_tendsto (K : StieltjesFunction ℝ)
    (H : ℝ≥0 → ℝ) (hH : Continuous H) (T : ℝ≥0) :
    Tendsto (dyadicWeightedIncrement H (fun t => K t.val) T) atTop
      (𝓝 (∫ r in Ioc (0 : ℝ) T.val, H r.toNNReal ∂K.measure)) := by
  have he : dyadicWeightedIncrement H (fun t => K t.val) T = dyadicStieltjesSum K H T :=
    funext (fun n => dyadicWeightedIncrement_stieltjes K H T n)
  rw [he]
  exact dyadicStieltjesSum_tendsto K H hH T

theorem dyadicWeightedIncrement_product_identity (K : StieltjesFunction ℝ)
    (q : ℝ≥0 → ℝ) (c : ℝ) (T : ℝ≥0) (n : ℕ) :
    (c - K T.val) * q T - (c - K 0) * q 0 =
      dyadicWeightedIncrement (fun t => c - K t.val) q T n - dyadicStieltjesRightSum K q T n :=
  dyadicStieltjes_product_identity K q c T n

end TimeTraps.Probability
