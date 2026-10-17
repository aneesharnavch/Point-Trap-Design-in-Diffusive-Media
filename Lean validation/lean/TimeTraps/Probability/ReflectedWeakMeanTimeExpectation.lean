module

public import TimeTraps.Probability.ReflectedWeakMeanTimeFinite
public import TimeTraps.Probability.ReflectedAtomicSurvivalExpectationTime

@[expose] public section

/-! Expectations of the actual finite-time killed identity for the
original full-H1 homogeneous weak mean state. Integrability of the
weighted state is derived from that identity and the genuine finite-time
survival integral. The original stochastic integral has proved mean zero. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

theorem reflectedWeakMeanTime_weighted_state_integrable
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => reflectedAtomicSurvival L D x E.geometry.site E.strength T ω *
      E.state (foldedTrajectory L D x brownianDyadicPath T ω)) brownianDyadicMeasure := by
  have hI := (Lp.memLp (brownianIntegral brownianDyadicPath_isPreBrownianReal
    (reflectedWeakMeanIntegrand E x T))).integrable (by norm_num)
  have hA := reflectedAtomicSurvival_time_integral_integrable L hD x E.geometry.site E.strength
    (fun i => (E.strength_pos i).le) T
  apply ((hI.sub hA).add (integrable_const (E.state (reflectedFold L x)))).congr
  filter_upwards [reflectedWeakMeanTime_finite E x T] with ω hω
  change (brownianIntegral brownianDyadicPath_isPreBrownianReal
    (reflectedWeakMeanIntegrand E x T) ω -
      (∫ r in (0 : ℝ)..T.val, reflectedAtomicSurvival L D x E.geometry.site E.strength r.toNNReal ω)) +
    E.state (reflectedFold L x) = _
  linarith

theorem reflectedWeakMeanTime_expected_finite
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicSurvival L D x E.geometry.site E.strength r.toNNReal ω) ∂brownianDyadicMeasure) =
      E.state (reflectedFold L x) -
        ∫ ω, reflectedAtomicSurvival L D x E.geometry.site E.strength T ω *
          E.state (foldedTrajectory L D x brownianDyadicPath T ω) ∂brownianDyadicMeasure := by
  have hI := (Lp.memLp (brownianIntegral brownianDyadicPath_isPreBrownianReal
    (reflectedWeakMeanIntegrand E x T))).integrable (by norm_num)
  have hA := reflectedAtomicSurvival_time_integral_integrable L hD x E.geometry.site E.strength
    (fun i => (E.strength_pos i).le) T
  have hV := reflectedWeakMeanTime_weighted_state_integrable E x T
  have he := integral_congr_ae (reflectedWeakMeanTime_finite E x T)
  rw [integral_sub hV (integrable_const _), integral_sub hI hA,
    brownianIntegral_mean brownianDyadicPath_isPreBrownianReal] at he
  simp only [integral_const, measureReal_def, measure_univ, ENNReal.toReal_one, one_smul, zero_sub] at he
  linarith

theorem reflectedWeakMeanTime_mean_survival_finite
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) (T : ℝ≥0) :
    (∫ r in (0 : ℝ)..T.val, reflectedAtomicMeanSurvival L D x E.geometry.site E.strength r.toNNReal) =
      E.state (reflectedFold L x) -
        ∫ ω, reflectedAtomicSurvival L D x E.geometry.site E.strength T ω *
          E.state (foldedTrajectory L D x brownianDyadicPath T ω) ∂brownianDyadicMeasure := by
  rw [← reflectedAtomicSurvival_mean_time_integral L hD x E.geometry.site E.strength
    (fun i => (E.strength_pos i).le) T]
  exact reflectedWeakMeanTime_expected_finite E x T

end TimeTraps.Probability
