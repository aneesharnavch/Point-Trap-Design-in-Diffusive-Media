module

public import TimeTraps.Probability.ReflectedInteriorTanakaContinuous

@[expose] public section

/-! The actual difference of two continuous stochastic integral paths
is represented on one compact-time event by the continuous-path linear
map of the integrand difference. Its norm is the maximal L2 control. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem brownianIntegralGlobalPath_sub_compact_ae (f g : BrownianIntegrand) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : BrownianCompactTime T,
      brownianIntegralGlobalPath f t.val ω - brownianIntegralGlobalPath g t.val ω =
        brownianIntegralContinuousL2 T (f - g) ω t := by
  have hsub : brownianIntegralContinuousL2 T (f - g) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianIntegralContinuousL2 T f ω - brownianIntegralContinuousL2 T g ω) := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  filter_upwards [brownianIntegralGlobalPath_compact_ae f T,
    brownianIntegralGlobalPath_compact_ae g T, hsub] with ω hf hg hs
  intro t
  rw [hf t, hg t, hs]
  rfl

theorem brownianIntegralGlobalPath_sub_compact_bound_ae (f g : BrownianIntegrand) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      |brownianIntegralGlobalPath f t ω - brownianIntegralGlobalPath g t ω| ≤
        ‖brownianIntegralContinuousL2 T (f - g) ω‖ := by
  filter_upwards [brownianIntegralGlobalPath_sub_compact_ae f g T] with ω he t ht
  rw [he ⟨t, zero_le, ht⟩]
  exact (brownianIntegralContinuousL2 T (f - g) ω).norm_coe_le_norm ⟨t, zero_le, ht⟩

theorem brownianIntegralCompactNorm_memLp (f : BrownianIntegrand) (T : ℝ≥0) :
    MemLp (fun ω => ‖brownianIntegralContinuousL2 T f ω‖) 2 brownianDyadicMeasure :=
  (Lp.memLp (brownianIntegralContinuousL2 T f)).norm

theorem brownianIntegralCompactNorm_L2norm (f : BrownianIntegrand) (T : ℝ≥0) :
    ‖(brownianIntegralCompactNorm_memLp f T).toLp
      (fun ω => ‖brownianIntegralContinuousL2 T f ω‖)‖ = ‖brownianIntegralContinuousL2 T f‖ := by
  rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_norm]

theorem reflectedInteriorCorrection_level_compact_bound_ae (L : ℝ) (hL : 0 < L)
    (a b : ℝ) (ha : a ∈ Ioo 0 L) (hb : b ∈ Ioo 0 L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      |reflectedInteriorCorrection x σ L a t ω - reflectedInteriorCorrection x σ L b t ω| ≤
        2 * |a - b| + ‖brownianIntegralContinuousL2 T
          (reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
            brownianDyadicPath_jointly_measurable L hL a ha x hσ T -
          reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
            brownianDyadicPath_jointly_measurable L hL b hb x hσ T) ω‖ := by
  let f := reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL a ha x hσ T
  let g := reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL b hb x hσ T
  filter_upwards [reflectedInteriorTanaka_continuous_ae L hL a ha x hσ T,
    reflectedInteriorTanaka_continuous_ae L hL b hb x hσ T,
    brownianIntegralGlobalPath_sub_compact_bound_ae f g T] with ω haT hbT hM t ht
  have hea := haT t ht
  have heb := hbT t ht
  have hbound (z : ℝ) : |(|z - a| - |z - b|)| ≤ |a - b| := by
    simpa only [show (z - a) - (z - b) = -(a - b) by ring, abs_neg] using
      abs_abs_sub_abs_le_abs_sub (z - a) (z - b)
  have hdiff : |(|reflectedFold L (affineBrownianInput x σ t ω) - a| - |reflectedFold L x - a|) -
      (|reflectedFold L (affineBrownianInput x σ t ω) - b| - |reflectedFold L x - b|)| ≤
      2 * |a - b| := by
    have h := abs_sub (|reflectedFold L (affineBrownianInput x σ t ω) - a| -
      |reflectedFold L (affineBrownianInput x σ t ω) - b|)
      (|reflectedFold L x - a| - |reflectedFold L x - b|)
    have hr : (|reflectedFold L (affineBrownianInput x σ t ω) - a| - |reflectedFold L x - a|) -
      (|reflectedFold L (affineBrownianInput x σ t ω) - b| - |reflectedFold L x - b|) =
      (|reflectedFold L (affineBrownianInput x σ t ω) - a| -
        |reflectedFold L (affineBrownianInput x σ t ω) - b|) -
      (|reflectedFold L x - a| - |reflectedFold L x - b|) := by ring
    rw [hr]
    have h₁ := hbound (reflectedFold L (affineBrownianInput x σ t ω))
    have h₂ := hbound (reflectedFold L x)
    exact h.trans (by linarith)
  have he : reflectedInteriorCorrection x σ L a t ω - reflectedInteriorCorrection x σ L b t ω =
      ((|reflectedFold L (affineBrownianInput x σ t ω) - a| - |reflectedFold L x - a|) -
      (|reflectedFold L (affineBrownianInput x σ t ω) - b| - |reflectedFold L x - b|)) -
      (brownianIntegralGlobalPath f t ω - brownianIntegralGlobalPath g t ω) := by
    change _ = _ - (reflectedInteriorKinkHorizonPath L hL a ha x hσ T t ω -
      reflectedInteriorKinkHorizonPath L hL b hb x hσ T t ω)
    linarith
  rw [he]
  exact (abs_sub _ _).trans (add_le_add hdiff (hM t ht))

end TimeTraps.Probability
