module

public import TimeTraps.Probability.ReflectedWeakMeanTimeTail
public import TimeTraps.Analysis.SurvivalIntegralLimit

@[expose] public section

/-! The actual survival expectation is integrable on the whole positive
time axis and its integral equals the original full-H1 weak mean state.
Both ordinary and extended nonnegative integrals are identified, using
the proved finite-time identity and vanishing terminal residual. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

theorem reflectedWeakMeanTime_mean_survival_integral
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    IntegrableOn (fun r : ℝ =>
      reflectedAtomicMeanSurvival L D x E.geometry.site E.strength r.toNNReal) (Ioi (0 : ℝ)) ∧
    (∫ r in Ioi (0 : ℝ), reflectedAtomicMeanSurvival L D x E.geometry.site E.strength r.toNNReal) =
      E.state (reflectedFold L x) ∧
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal
      (reflectedAtomicMeanSurvival L D x E.geometry.site E.strength r.toNNReal)) =
      ENNReal.ofReal (E.state (reflectedFold L x)) :=
  survivalIntegralLimit_of_antitone
    (fun t => (reflectedAtomicMeanSurvival_bounds L hD x E.geometry.site E.strength
      (fun i => (E.strength_pos i).le) t).1)
    (reflectedAtomicMeanSurvival_antitone L hL D hD x E.geometry.site E.strength
      (fun i => (E.strength_pos i).le))
    (reflectedWeakMeanTime_mean_survival_tendsto E x)

theorem reflectedWeakMeanTime_mean_survival_integral_at_start
    (E : IntervalDesign (homogeneous L D hL hD) n K) {x : ℝ} (hx : x ∈ Icc 0 L) :
    IntegrableOn (fun r : ℝ =>
      reflectedAtomicMeanSurvival L D x E.geometry.site E.strength r.toNNReal) (Ioi (0 : ℝ)) ∧
    (∫ r in Ioi (0 : ℝ), reflectedAtomicMeanSurvival L D x E.geometry.site E.strength r.toNNReal) =
      E.state x ∧
    (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal
      (reflectedAtomicMeanSurvival L D x E.geometry.site E.strength r.toNNReal)) =
      ENNReal.ofReal (E.state x) := by
  simpa only [reflectedFold_eq_self L hL x hx] using reflectedWeakMeanTime_mean_survival_integral E x

end TimeTraps.Probability
