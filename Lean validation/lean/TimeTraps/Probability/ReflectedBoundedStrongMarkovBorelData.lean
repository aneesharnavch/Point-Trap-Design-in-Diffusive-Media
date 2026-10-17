module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkov
public import TimeTraps.Probability.ReflectedGaussianTransition
public import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

@[expose] public section

/-! Continuous state representatives and Gaussian continuation formulas
for extending the proved stopping identity from continuous spatial tests
to bounded Borel tests by finite-measure uniqueness. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal BoundedContinuousFunction

def reflectedMarkovState (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (t : ℝ≥0) (ω : BrownianCompletedSample) : Icc (0 : ℝ) L :=
  reflectedIntervalFold L hL (x + Real.sqrt (2 * D) * reflectedMarkovBrownianPath t ω)

theorem reflectedMarkovState_continuous (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (ω : BrownianCompletedSample) : Continuous (fun t => reflectedMarkovState L hL D x t ω) :=
  (reflectedIntervalFold L hL).continuous.comp
    (continuous_const.add (continuous_const.mul (reflectedMarkovBrownianPath_continuous ω)))

theorem reflectedMarkovState_stronglyAdapted (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    StronglyAdapted brownianCompletedFiltration.rightCont (reflectedMarkovState L hL D x) := by
  intro t
  exact ((reflectedIntervalFold L hL).continuous.comp_stronglyMeasurable
    (stronglyMeasurable_const.add (stronglyMeasurable_const.mul
      (reflectedMarkovBrownianPath_stronglyAdapted t)))).mono
        (brownianCompletedFiltration.le_rightCont t)

theorem reflectedMarkovState_stopped_stronglyMeasurable
    (L : ℝ) (hL : 0 < L) (D x : ℝ) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    StronglyMeasurable[hτ.measurableSpace] (fun ω => reflectedMarkovState L hL D x (τ ω) ω) :=
  (measurable_stoppedValue
    ((reflectedMarkovState_stronglyAdapted L hL D x).isStronglyProgressive_of_continuous
      (reflectedMarkovState_continuous L hL D x)) hτ).stronglyMeasurable

def reflectedMarkovTestRestrict (L : ℝ) (f : ℝ →ᵇ ℝ) : C(Icc (0 : ℝ) L, ℝ) :=
  ⟨fun y => f y.val, f.continuous.comp continuous_subtype_val⟩

theorem reflectedMarkovTestRestrict_observation (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : ℝ →ᵇ ℝ) (t : ℝ≥0) (ω : BrownianCompletedSample) :
    reflectedMarkovObservation L hL D x (reflectedMarkovTestRestrict L f) t ω =
      f (reflectedMarkovState L hL D x t ω).val := rfl

theorem reflectedMarkovTestRestrict_gaussian (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (f : ℝ →ᵇ ℝ) (h t : ℝ≥0) (ω : BrownianCompletedSample) :
    reflectedMarkovObservation L hL D x
      (reflectedFellerTimeOperator L hL D h.val (reflectedMarkovTestRestrict L f)) t ω =
      ∫ z, f (reflectedFold L ((reflectedMarkovState L hL D x t ω).val +
        Real.sqrt (Real.toNNReal (2 * D * h.val) : ℝ) * z)) ∂gaussianReal 0 1 := by
  exact reflectedFellerValue_apply L hL (Real.toNNReal (2 * D * h.val))
    (reflectedMarkovTestRestrict L f) (reflectedMarkovState L hL D x t ω)

theorem reflectedMarkovState_actual_ae (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ t : ℝ≥0,
      (reflectedMarkovState L hL D x t ω).val = foldedTrajectory L D x brownianDyadicPath t ω := by
  filter_upwards [reflectedMarkovBrownianPath_ae_all] with ω hω
  intro t
  exact congrArg (fun z => reflectedFold L (x + Real.sqrt (2 * D) * z)) (hω t)

end TimeTraps.Probability

end
