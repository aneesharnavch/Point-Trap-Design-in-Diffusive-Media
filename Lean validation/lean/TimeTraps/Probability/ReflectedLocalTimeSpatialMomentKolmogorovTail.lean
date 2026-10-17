module

public import TimeTraps.Probability.BrownianIntegralFourthIncrement
public import TimeTraps.Probability.BrownianSequenceContinuity

@[expose] public section

/-! Fourth-moment tail bounds and stochastic continuity in a metric
space, used for the spatial local-time continuous modification. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] {P : Measure Ω}
variable {X : ℝ≥0 → Ω → E} {C : ℝ}

theorem fourthMoment_increment_tail {s t : ℝ≥0}
    (hi : Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist s t ^ 2)
    {ε : ℝ} (hε : 0 < ε) :
    P.real {ω | ε ≤ dist (X s ω) (X t ω)} ≤ C * dist s t ^ 2 / ε ^ 4 := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun ω => dist (X s ω) (X t ω) ^ 4)
    (Eventually.of_forall (fun _ => by positivity)) hi (ε ^ 4)
  have he : {ω | ε ^ 4 ≤ dist (X s ω) (X t ω) ^ 4} =
      {ω | ε ≤ dist (X s ω) (X t ω)} := by
    ext ω
    exact pow_le_pow_iff_left₀ hε.le dist_nonneg (by norm_num)
  rw [he] at h
  exact (le_div_iff₀ (pow_pos hε 4)).mpr (by nlinarith [h.trans hb])

theorem fourthMoment_tendstoInMeasure [IsFiniteMeasure P]
    (hi : ∀ s t, Integrable (fun ω => dist (X s ω) (X t ω) ^ 4) P)
    (hb : ∀ s t, (∫ ω, dist (X s ω) (X t ω) ^ 4 ∂P) ≤ C * dist s t ^ 2)
    {u : ℕ → ℝ≥0} {t : ℝ≥0} (hu : Tendsto u atTop (𝓝 t)) :
    TendstoInMeasure P (fun n => X (u n)) atTop (X t) := by
  apply tendstoInMeasure_iff_measureReal_dist.mpr
  intro ε hε
  have hp : Tendsto (fun n => C * dist (u n) t ^ 2 / ε ^ 4) atTop (𝓝 0) := by
    simpa using (((hu.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => t) atTop (𝓝 t))).pow 2).const_mul C).div_const (ε ^ 4)
  exact squeeze_zero (fun _ => measureReal_nonneg)
    (fun n => fourthMoment_increment_tail (hi (u n) t) (hb (u n) t) hε) hp

end TimeTraps.Probability
