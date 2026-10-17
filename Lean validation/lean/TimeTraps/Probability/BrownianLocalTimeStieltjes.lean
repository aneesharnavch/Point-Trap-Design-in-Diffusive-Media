module

public import TimeTraps.Probability.BrownianLocalTimeSupportLocal
public import TimeTraps.Analysis.StieltjesLocalSupport

@[expose] public section

/-! Extend the actual global Tanaka path by zero to negative real times.
Its continuous nondecreasing extension defines a genuine atomless
Stieltjes measure, with the original path increments on finite intervals. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def brownianLocalTimeRealPath (a t : ℝ) (ω : ℕ → ℝ) : ℝ :=
  brownianLocalTimeGlobalPath a t.toNNReal ω

theorem brownianLocalTimeRealPath_of_nonpos (a : ℝ) {t : ℝ} (ht : t ≤ 0) (ω : ℕ → ℝ) :
    brownianLocalTimeRealPath a t ω = 0 := by
  rw [brownianLocalTimeRealPath, Real.toNNReal_of_nonpos ht, brownianLocalTimeGlobalPath_zero]

theorem brownianLocalTimeRealPath_coe (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    brownianLocalTimeRealPath a (t : ℝ) ω = brownianLocalTimeGlobalPath a t ω := by
  rw [brownianLocalTimeRealPath, Real.toNNReal_coe]

theorem brownianLocalTimeRealPath_continuous (a : ℝ) (ω : ℕ → ℝ) :
    Continuous (fun t => brownianLocalTimeRealPath a t ω) :=
  (brownianLocalTimeGlobalPath_continuous a ω).comp continuous_real_toNNReal

theorem brownianLocalTimeRealPath_monotone (a : ℝ) (ω : ℕ → ℝ) :
    Monotone (fun t => brownianLocalTimeRealPath a t ω) :=
  (brownianLocalTimeGlobalPath_monotone a ω).comp Real.toNNReal_monotone

noncomputable def brownianLocalTimeStieltjes (a : ℝ) (ω : ℕ → ℝ) : StieltjesFunction ℝ :=
  continuousStieltjesFunction (fun t => brownianLocalTimeRealPath a t ω)
    (brownianLocalTimeRealPath_monotone a ω) (brownianLocalTimeRealPath_continuous a ω)

noncomputable def brownianLocalTimeMeasure (a : ℝ) (ω : ℕ → ℝ) : Measure ℝ :=
  (brownianLocalTimeStieltjes a ω).measure

theorem brownianLocalTimeMeasure_Ioc (a : ℝ) (ω : ℕ → ℝ) (S T : ℝ≥0) :
    brownianLocalTimeMeasure a ω (Ioc (S : ℝ) (T : ℝ)) =
      ENNReal.ofReal (brownianLocalTimeGlobalPath a T ω - brownianLocalTimeGlobalPath a S ω) := by
  change (brownianLocalTimeStieltjes a ω).measure (Ioc (S : ℝ) (T : ℝ)) = _
  rw [StieltjesFunction.measure_Ioc]
  change ENNReal.ofReal (brownianLocalTimeRealPath a T ω - brownianLocalTimeRealPath a S ω) = _
  rw [brownianLocalTimeRealPath_coe, brownianLocalTimeRealPath_coe]

theorem brownianLocalTimeMeasure_singleton (a : ℝ) (ω : ℕ → ℝ) (t : ℝ) :
    brownianLocalTimeMeasure a ω {t} = 0 :=
  continuousStieltjesFunction_measure_singleton _ _ _ t

theorem brownianLocalTimeMeasure_Ioc_zero (a : ℝ) (ω : ℕ → ℝ) (T : ℝ≥0) :
    brownianLocalTimeMeasure a ω (Ioc (0 : ℝ) (T : ℝ)) =
      ENNReal.ofReal (brownianLocalTimeGlobalPath a T ω) := by
  simpa only [NNReal.coe_zero, brownianLocalTimeGlobalPath_zero, sub_zero] using
    brownianLocalTimeMeasure_Ioc a ω 0 T

end TimeTraps.Probability
