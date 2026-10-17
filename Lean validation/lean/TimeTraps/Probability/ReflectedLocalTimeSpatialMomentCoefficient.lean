module

public import TimeTraps.Probability.ReflectedInteriorKinkIntegrandData

@[expose] public section

/-! The difference of the two actual reflected Tanaka coefficients is
bounded, measurable, and continuous off an explicit countable union.
Its square vanishes outside a shrinking physical spatial band. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory TimeTraps.Analysis
open scoped NNReal ENNReal

noncomputable def reflectedKinkDifference (L a b x σ z : ℝ) : ℝ :=
  σ * (reflectedInteriorKinkCoefficient L a x σ z -
    reflectedInteriorKinkCoefficient L b x σ z)

theorem reflectedKinkDifference_measurable (L : ℝ) (hL : 0 < L) (a b x σ : ℝ) :
    Measurable (reflectedKinkDifference L a b x σ) :=
  measurable_const.mul ((reflectedInteriorKinkCoefficient_measurable L hL a x σ).sub
    (reflectedInteriorKinkCoefficient_measurable L hL b x σ))

theorem reflectedKinkDifference_bound (L : ℝ) (hL : 0 < L) (a b x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (z : ℝ) : |reflectedKinkDifference L a b x σ z| ≤ 2 * σ := by
  unfold reflectedKinkDifference
  rw [abs_mul, abs_of_pos hσ]
  have h := (abs_sub _ _).trans (add_le_add
    (reflectedInteriorKinkCoefficient_bound L hL a x σ z)
    (reflectedInteriorKinkCoefficient_bound L hL b x σ z))
  nlinarith

theorem reflectedKinkDifference_continuousAt (L : ℝ) (hL : 0 < L)
    (a b : ℝ) (ha : a ∈ Ioo 0 L) (hb : b ∈ Ioo 0 L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (z : ℝ)
    (hz : z ∉ reflectedInteriorKinkExceptional L a x σ ∪ reflectedInteriorKinkExceptional L b x σ) :
    ContinuousAt (reflectedKinkDifference L a b x σ) z :=
  continuousAt_const.mul ((reflectedInteriorKinkCoefficient_continuousAt L hL a ha x hσ z
    (fun h => hz (Or.inl h))).sub
    (reflectedInteriorKinkCoefficient_continuousAt L hL b hb x hσ z (fun h => hz (Or.inr h))))

theorem brownianSign_sub_eq_of_outside_band (a b y : ℝ)
    (hy : ¬ |y - a| < 2 * |a - b|) : Real.sign (y - a) = Real.sign (y - b) := by
  by_cases hab : a = b
  · subst b; rfl
  have hd : 0 < |a - b| := abs_pos.mpr (sub_ne_zero.mpr hab)
  have hya : 2 * |a - b| ≤ |y - a| := le_of_not_gt hy
  have hab1 := le_abs_self (a - b)
  have hab2 := neg_le_abs (a - b)
  rcases lt_or_ge (y - a) 0 with hn | hp
  · have hn' : y - b < 0 := by rw [abs_of_neg hn] at hya; linarith
    rw [Real.sign_of_neg hn, Real.sign_of_neg hn']
  · have hp' : 0 < y - a := by rw [abs_of_nonneg hp] at hya; linarith
    have hp'' : 0 < y - b := by rw [abs_of_nonneg hp] at hya; linarith
    rw [Real.sign_of_pos hp', Real.sign_of_pos hp'']

theorem reflectedKinkDifference_square_band (L : ℝ) (hL : 0 < L) (a b x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (z : ℝ) :
    reflectedKinkDifference L a b x σ z ^ 2 ≤ 4 * σ ^ 2 *
      (if |reflectedFold L (x + σ * z) - a| < 2 * |a - b| then 1 else 0) := by
  split_ifs with hband
  · have h := reflectedKinkDifference_bound L hL a b x hσ z
    have hs := (sq_le_sq₀ (abs_nonneg _) (by positivity : 0 ≤ 2 * σ)).mpr h
    rw [sq_abs] at hs
    nlinarith
  · have hs := brownianSign_sub_eq_of_outside_band a b (reflectedFold L (x + σ * z)) hband
    unfold reflectedKinkDifference reflectedInteriorKinkCoefficient reflectedInteriorTanakaSlope
    rw [hs, sub_self, mul_zero]
    simp

end TimeTraps.Probability
