module

public import TimeTraps.Probability.ReversibleResistanceCanonicalLocalTimeRevuzData

@[expose] public section

/-! Revuz normalization of the actual canonical positive continuous
additive functional, using its own Stieltjes contact measure. The
identification is proved on one all-time event for each fixed site. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistanceCanonicalRevuzContact_integrable (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) (g : ℝ → ℝ) (T : ℝ≥0) :
    Integrable (reversibleResistanceCanonicalRevuzContact A x a g T) brownianCompletedMeasure := by
  have hi := (completedMeasure_integrable brownianDyadicMeasure
    ((reversibleResistanceLocalTime_memLp_two A x a T).integrable (by norm_num))).const_mul (g a)
  apply hi.congr
  filter_upwards [reversibleResistanceCanonicalRevuzContact_ae A x ha] with ω hω
  exact (hω g T).symm

theorem reversibleResistanceCanonicalRevuzContact_mean (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) (g : ℝ → ℝ) (T : ℝ≥0) :
    (∫ ω, reversibleResistanceCanonicalRevuzContact A x a g T ω ∂brownianCompletedMeasure) =
      ∫ ω, reversibleResistanceRevuzContact A x a g T ω ∂brownianDyadicMeasure := by
  calc
    _ = ∫ ω : BrownianCompletedSample, g a * reversibleResistanceLocalTime A x a T ω
        ∂brownianCompletedMeasure := by
      apply integral_congr_ae
      filter_upwards [reversibleResistanceCanonicalRevuzContact_ae A x ha] with ω hω
      exact hω g T
    _ = g a * ∫ ω, reversibleResistanceLocalTime A x a T ω ∂brownianDyadicMeasure := by
      exact (integral_const_mul (μ := brownianCompletedMeasure) (g a)
        (fun ω : BrownianCompletedSample => reversibleResistanceLocalTime A x a T ω)).trans
          (congrArg (fun v : ℝ => g a * v) (completedMeasure_integral brownianDyadicMeasure
            (reversibleResistanceLocalTime_memLp_two A x a T).aestronglyMeasurable))
    _ = _ := (reversibleResistanceRevuzContact_mean A x ha g T).symm

theorem reversibleResistanceCanonicalRevuzContact_speed_integrable (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc A.source.left A.source.right)) (g : ℝ → ℝ) (T : ℝ≥0) :
    Integrable (fun x => f x.val * (∫ ω, reversibleResistanceCanonicalRevuzContact A x.val a.val g T ω
      ∂brownianCompletedMeasure)) (reversibleResistanceSpeedMeasure A) := by
  apply (reversibleResistanceRevuzContact_speed_integrable A a hf g T).congr
  exact Eventually.of_forall (fun x => congrArg (fun v : ℝ => f x.val * v)
    (reversibleResistanceCanonicalRevuzContact_mean A x.val a.property g T).symm)

theorem reversibleResistanceCanonicalRevuzContact_speed_identity (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc A.source.left A.source.right)) (g : ℝ → ℝ) (T : ℝ≥0) :
    (∫ x, f x.val * (∫ ω, reversibleResistanceCanonicalRevuzContact A x.val a.val g T ω
      ∂brownianCompletedMeasure) ∂reversibleResistanceSpeedMeasure A) =
      g a.val * ∫ s in (0 : ℝ)..T.val, reversibleResistanceTransition A s.toNNReal f a.val := by
  calc
    _ = ∫ x, f x.val * (∫ ω, reversibleResistanceRevuzContact A x.val a.val g T ω
        ∂brownianDyadicMeasure) ∂reversibleResistanceSpeedMeasure A := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => congrArg (fun v : ℝ => f x.val * v)
        (reversibleResistanceCanonicalRevuzContact_mean A x.val a.property g T))
    _ = _ := reversibleResistanceRevuzContact_speed_identity A a hf g T

theorem reversibleResistanceCanonicalRevuz_limit_speedMeasure (A : IntervalMedium)
    (a : Ioo A.source.left A.source.right) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Icc A.source.left A.source.right)) (g : ℝ → ℝ) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ x, f x.val *
      (∫ ω, reversibleResistanceCanonicalRevuzContact A x.val a.val g t.toNNReal ω ∂brownianCompletedMeasure)
        ∂reversibleResistanceSpeedMeasure A) (𝓝[>] 0) (𝓝 (f a.val * g a.val)) := by
  apply (reversibleResistanceRevuz_limit_speedMeasure A a hf g).congr
  intro t
  congr 1
  exact (reversibleResistanceRevuzContact_speed_identity A a hf g t.toNNReal).trans
    (reversibleResistanceCanonicalRevuzContact_speed_identity A a hf g t.toNNReal).symm

end TimeTraps.Probability
