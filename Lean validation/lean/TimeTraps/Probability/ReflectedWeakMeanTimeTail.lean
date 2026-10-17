module

public import TimeTraps.Probability.ReflectedWeakMeanTimeExpectation
public import TimeTraps.Probability.ReflectedAtomicSurvivalExpectationTail
public import TimeTraps.Interval.ReflectedMeanKinkBounds

@[expose] public section

/-! The original homogeneous weak solution supplies the finite expected
survival-time bound. Its positivity and boundedness then force the actual
mean survival and the terminal weighted-state residual to vanish. Thus
the expected finite-time survival integrals converge to the weak state;
no finite-lifetime or infinite-integrability premise is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {L D K : ℝ} {n : ℕ} {hL : 0 < L} {hD : 0 < D}

def reflectedWeakMeanResidual (E : IntervalDesign (homogeneous L D hL hD) n K)
    (x : ℝ) (T : ℝ≥0) : ℝ :=
  ∫ ω, reflectedAtomicSurvival L D x E.geometry.site E.strength T ω *
    E.state (foldedTrajectory L D x brownianDyadicPath T ω) ∂brownianDyadicMeasure

theorem reflectedWeakMeanResidual_nonneg
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) (T : ℝ≥0) :
    0 ≤ reflectedWeakMeanResidual E x T :=
  integral_nonneg (fun ω => mul_nonneg
    (reflectedAtomicSurvival_bounds L hD x E.geometry.site E.strength
      (fun i => (E.strength_pos i).le) T ω).1.le
    (E.homogeneous_state_pos _ (foldedTrajectory_mem L hL D x brownianDyadicPath T ω)).le)

theorem reflectedWeakMeanTime_expected_bound
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicSurvival L D x E.geometry.site E.strength r.toNNReal ω) ∂brownianDyadicMeasure) ≤
        E.state (reflectedFold L x) := by
  rw [reflectedWeakMeanTime_expected_finite E x T]
  exact sub_le_self _ (reflectedWeakMeanResidual_nonneg E x T)

theorem reflectedWeakMeanTime_survival_tendsto
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    Tendsto (reflectedAtomicMeanSurvival L D x E.geometry.site E.strength) atTop (𝓝 0) :=
  reflectedAtomicMeanSurvival_tendsto_of_expected_bound L hL D hD x E.geometry.site E.strength
    (fun i => (E.strength_pos i).le) (reflectedWeakMeanTime_expected_bound E x)

theorem reflectedWeakMeanResidual_bound
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) {C : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) L, |E.state z| ≤ C) (T : ℝ≥0) :
    |reflectedWeakMeanResidual E x T| ≤
      C * reflectedAtomicMeanSurvival L D x E.geometry.site E.strength T := by
  rw [abs_of_nonneg (reflectedWeakMeanResidual_nonneg E x T)]
  have hW := reflectedAtomicSurvival_integrable L hD x E.geometry.site E.strength
    (fun i => (E.strength_pos i).le) T
  calc
    _ ≤ ∫ ω, C * reflectedAtomicSurvival L D x E.geometry.site E.strength T ω
        ∂brownianDyadicMeasure := by
      apply integral_mono (reflectedWeakMeanTime_weighted_state_integrable E x T) (hW.const_mul C)
      intro ω
      have hu := (le_abs_self (E.state (foldedTrajectory L D x brownianDyadicPath T ω))).trans
        (hC _ (foldedTrajectory_mem L hL D x brownianDyadicPath T ω))
      have hw := (reflectedAtomicSurvival_bounds L hD x E.geometry.site E.strength
        (fun i => (E.strength_pos i).le) T ω).1.le
      exact (mul_le_mul_of_nonneg_left hu hw).trans_eq (mul_comm _ _)
    _ = _ := integral_const_mul _ _

theorem reflectedWeakMeanResidual_tendsto
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    Tendsto (reflectedWeakMeanResidual E x) atTop (𝓝 0) := by
  obtain ⟨C, _hCnonneg, hC⟩ := E.homogeneous_state_bounded
  exact reflectedAtomicMeanSurvival_residual_tendsto_of_expected_bound L hL D hD x
    E.geometry.site E.strength (fun i => (E.strength_pos i).le)
    (reflectedWeakMeanTime_expected_bound E x) (reflectedWeakMeanResidual_bound E x hC)

theorem reflectedWeakMeanTime_expected_tendsto
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    Tendsto (fun T : ℝ≥0 => ∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicSurvival L D x E.geometry.site E.strength r.toNNReal ω) ∂brownianDyadicMeasure)
      atTop (𝓝 (E.state (reflectedFold L x))) := by
  have h := (reflectedWeakMeanResidual_tendsto E x).const_sub (E.state (reflectedFold L x))
  simpa only [reflectedWeakMeanTime_expected_finite, reflectedWeakMeanResidual, sub_zero] using h

theorem reflectedWeakMeanTime_mean_survival_tendsto
    (E : IntervalDesign (homogeneous L D hL hD) n K) (x : ℝ) :
    Tendsto (fun T : ℝ≥0 => ∫ r in (0 : ℝ)..T.val,
      reflectedAtomicMeanSurvival L D x E.geometry.site E.strength r.toNNReal)
      atTop (𝓝 (E.state (reflectedFold L x))) := by
  have h := reflectedWeakMeanTime_expected_tendsto E x
  simpa only [reflectedAtomicSurvival_mean_time_integral L hD x E.geometry.site E.strength
    (fun i => (E.strength_pos i).le)] using h

end TimeTraps.Probability

end
