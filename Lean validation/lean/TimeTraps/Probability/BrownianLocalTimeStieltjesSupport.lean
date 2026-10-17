module

public import TimeTraps.Probability.BrownianLocalTimeStieltjes

@[expose] public section

/-! At each fixed level, the actual Stieltjes measure of the global
Tanaka path is supported on nonnegative times at which the original
Brownian trajectory equals that level. The event is the previously
proved measurable support event; no new level intersection is taken. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem brownianLocalTimeMeasure_support {a : ℝ} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeSupportRegular a ω) :
    (brownianLocalTimeMeasure a ω).support ⊆
      {t : ℝ | 0 ≤ t ∧ brownianDyadicPath t.toNNReal ω = a} := by
  intro t ht
  have hnonneg : 0 ≤ t := by
    by_contra hn
    have hneg : t < 0 := lt_of_not_ge hn
    have hflat : ∀ᶠ s in 𝓝 t,
        brownianLocalTimeRealPath a s ω = brownianLocalTimeRealPath a t ω := by
      filter_upwards [Iio_mem_nhds hneg] with s hs
      rw [brownianLocalTimeRealPath_of_nonpos a (show s ≤ 0 from (show s < 0 from hs).le),
        brownianLocalTimeRealPath_of_nonpos a hneg.le]
    exact (continuousStieltjesFunction_notMem_support _
      (brownianLocalTimeRealPath_monotone a ω) (brownianLocalTimeRealPath_continuous a ω) t hflat) ht
  refine ⟨hnonneg, ?_⟩
  by_contra hne
  have hlocal := brownianLocalTimeSupportRegular_locally_constant hω t.toNNReal hne
  have hflat : ∀ᶠ s in 𝓝 t,
      brownianLocalTimeRealPath a s ω = brownianLocalTimeRealPath a t ω :=
    continuous_real_toNNReal.continuousAt.tendsto.eventually hlocal
  exact (continuousStieltjesFunction_notMem_support _
    (brownianLocalTimeRealPath_monotone a ω) (brownianLocalTimeRealPath_continuous a ω) t hflat) ht

theorem brownianLocalTimeMeasure_carried_by_level {a : ℝ} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeSupportRegular a ω) :
    ∀ᵐ t ∂brownianLocalTimeMeasure a ω, 0 ≤ t ∧ brownianDyadicPath t.toNNReal ω = a := by
  have hs : ∀ᵐ t ∂brownianLocalTimeMeasure a ω, t ∈ (brownianLocalTimeMeasure a ω).support :=
    (brownianLocalTimeMeasure a ω).support_mem_ae
  exact hs.mono (fun _ ht => brownianLocalTimeMeasure_support hω ht)

theorem brownianLocalTimeMeasure_support_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, (brownianLocalTimeMeasure a ω).support ⊆
      {t : ℝ | 0 ≤ t ∧ brownianDyadicPath t.toNNReal ω = a} :=
  (brownianLocalTimeSupportRegular_ae a).mono (fun _ hω => brownianLocalTimeMeasure_support hω)

end TimeTraps.Probability
