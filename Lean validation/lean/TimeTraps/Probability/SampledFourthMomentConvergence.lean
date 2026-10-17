module

public import TimeTraps.Probability.SampledFourthMomentTail

@[expose] public section

/-! Moment continuity for a sequence of observations approaching one
additional time. This requires no already existing all-time process. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E]
variable {P : Measure Ω} [IsFiniteMeasure P]

theorem sampledFourthMoment_tendstoInMeasure {Y : ℕ → Ω → E} {Z : Ω → E}
    {u : ℕ → ℝ≥0} {t : ℝ≥0} {C : ℝ}
    (hi : ∀ n, Integrable (fun ω => dist (Y n ω) (Z ω) ^ 4) P)
    (hb : ∀ n, (∫ ω, dist (Y n ω) (Z ω) ^ 4 ∂P) ≤ C * dist (u n) t ^ 2)
    (hu : Tendsto u atTop (𝓝 t)) : TendstoInMeasure P Y atTop Z := by
  apply tendstoInMeasure_iff_measureReal_dist.mpr
  intro ε hε
  have hp : Tendsto (fun n => C * dist (u n) t ^ 2 / ε ^ 4) atTop (𝓝 0) := by
    simpa using (((hu.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t))).pow 2).const_mul C).div_const (ε ^ 4)
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => fourthMoment_dist_tail_of_bound (hi n) (hb n) hε) hp

end TimeTraps.Probability
