module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentKolmogorovTail

@[expose] public section

/-! The fourth-moment tail estimate for two genuine sampled random
variables; it requires no process already indexed by every real time. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter

variable {Ω E : Type*} [MeasurableSpace Ω] [MetricSpace E] {P : Measure Ω}

theorem fourthMoment_dist_tail_of_bound {f g : Ω → E} {M ε : ℝ}
    (hi : Integrable (fun ω => dist (f ω) (g ω) ^ 4) P)
    (hb : (∫ ω, dist (f ω) (g ω) ^ 4 ∂P) ≤ M) (hε : 0 < ε) :
    P.real {ω | ε ≤ dist (f ω) (g ω)} ≤ M / ε ^ 4 := by
  have h := mul_meas_ge_le_integral_of_nonneg
    (μ := P) (f := fun ω => dist (f ω) (g ω) ^ 4)
    (Eventually.of_forall (fun _ => by positivity)) hi (ε ^ 4)
  have he : {ω | ε ^ 4 ≤ dist (f ω) (g ω) ^ 4} = {ω | ε ≤ dist (f ω) (g ω)} := by
    ext ω
    exact pow_le_pow_iff_left₀ hε.le dist_nonneg (by norm_num)
  rw [he] at h
  exact (le_div_iff₀ (pow_pos hε 4)).mpr (by nlinarith [h.trans hb])

end TimeTraps.Probability
