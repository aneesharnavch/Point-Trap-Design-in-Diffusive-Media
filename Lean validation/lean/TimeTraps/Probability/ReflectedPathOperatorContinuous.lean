module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovPath

@[expose] public section

/-! Fresh compact reflected paths depend continuously on their initial
point for every sample. Bounded continuous path tests therefore have
continuous actual expectations. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal

theorem reflectedMarkovFreshPath_continuous_initial
    (L : ℝ) (hL : 0 < L) (D : ℝ) (H : ℝ≥0) (ω : BrownianCompletedSample) :
    Continuous (fun y : Icc (0 : ℝ) L => reflectedMarkovFreshPath L hL D H (y, ω)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun q : Icc (0 : ℝ) L × Icc (0 : ℝ≥0) H =>
    reflectedMarkovState L hL D q.1.val (0 + q.2.val) ω)
  simp only [zero_add]
  exact (reflectedIntervalFold L hL).continuous.comp
    ((continuous_subtype_val.comp continuous_fst).add
      (continuous_const.mul ((reflectedMarkovBrownianPath_continuous ω).comp
        (continuous_subtype_val.comp continuous_snd))))

theorem reflectedMarkovPathOperator_continuous
    (L : ℝ) (hL : 0 < L) (D : ℝ) (H : ℝ≥0)
    {g : ReflectedMarkovPath L H → ℝ} (hg : Continuous g)
    {M : ℝ} (hb : ∀ p, |g p| ≤ M) :
    Continuous (reflectedMarkovPathOperator L hL D H g) := by
  apply continuous_of_dominated
    (fun y => ((hg.measurable.comp (reflectedMarkovFreshPath_measurable L hL D H)).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (fun y => Eventually.of_forall (fun ω => hb (reflectedMarkovFreshPath L hL D H (y, ω))))
    (integrable_const M)
    (Eventually.of_forall (fun ω => hg.comp (reflectedMarkovFreshPath_continuous_initial L hL D H ω)))

end TimeTraps.Probability

end
