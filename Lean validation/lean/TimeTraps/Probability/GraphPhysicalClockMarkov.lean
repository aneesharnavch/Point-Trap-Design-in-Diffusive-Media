module

public import TimeTraps.Probability.GraphPhysicalClockCocycle
public import TimeTraps.Probability.GraphPhysicalClockLaw
public import TimeTraps.Probability.GraphConservativeFuturePath

@[expose] public section

/-! The actual physical future law at each physical time follows from
the original whole-path strong Markov law at the bounded inverse clock.
The conditional sigma algebra is explicitly the original stopped past. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalPathKernel_integral
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (y : GraphRealization P.geometry)
    {g : GraphContinuousPath P.geometry → ℝ} (hg : Measurable g) :
    (∫ q, g q ∂P.physicalPathKernel hκ b hb y) =
      ∫ q, g (P.geometry.physicalPath b hb q) ∂P.continuousPathLaw hκ y := by
  change (∫ q, g q ∂P.physicalPathLaw hκ b hb y) = _
  rw [P.physicalPathLaw_eq_map]
  exact integral_map (P.geometry.physicalPath_measurable b hb).aemeasurable hg.aestronglyMeasurable

theorem GraphShiftedContactOperatorProblem.physicalPath_future_condExp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (x : GraphRealization P.geometry) (s : ℝ≥0)
    {g : GraphContinuousPath P.geometry → ℝ} (hg : Measurable g)
    {C : ℝ} (hC : ∀ p, ‖g p‖ ≤ C) :
    (P.continuousPathLaw hκ x)[
      (fun p => g (graphContinuousPathShift P.geometry s (P.geometry.physicalPath b hb p))) |
        (P.geometry.physicalInverseClock_isStoppingTime b hb s).measurableSpace]
      =ᵐ[P.continuousPathLaw hκ x]
        (fun p => ∫ q, g q ∂P.physicalPathKernel hκ b hb (P.geometry.physicalPath b hb p s)) := by
  have he := P.continuousPathLaw_future_strongMarkov hκ x
    (P.geometry.physicalInverseClock_isStoppingTime b hb s)
    (hg.comp (P.geometry.physicalPath_measurable b hb))
    (fun p => hC (P.geometry.physicalPath b hb p))
  simpa only [Function.comp_def, ← P.geometry.physicalPath_shift,
    P.physicalPathKernel_integral hκ b hb _ hg, P.geometry.physicalPath_apply,
    P.continuousPathKernel_apply] using he

end TimeTraps.Analysis
