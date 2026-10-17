module

public import TimeTraps.Probability.GraphPhysicalClockPath
public import TimeTraps.Probability.GraphPhysicalSpeedIndependence
public import TimeTraps.Probability.GraphConservativePathKernel

@[expose] public section

/-! The physical continuous-path probability law is the literal inverse
clock pushforward. Its starting-state dependence is a genuine Markov
kernel, and it is independent of the chosen positive vertex value. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.physicalPathKernel
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (b : ℝ) (hb : 0 < b) :
    Kernel (GraphRealization P.geometry) (GraphContinuousPath P.geometry) :=
  (P.continuousPathKernel hκ).map (P.geometry.physicalPath b hb)

instance GraphShiftedContactOperatorProblem.physicalPathKernel_isMarkov
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (b : ℝ) (hb : 0 < b) :
    IsMarkovKernel (P.physicalPathKernel hκ b hb) := by
  unfold physicalPathKernel
  exact Kernel.IsMarkovKernel.map _ (P.geometry.physicalPath_measurable b hb)

noncomputable def GraphShiftedContactOperatorProblem.physicalPathLaw
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (b : ℝ) (hb : 0 < b)
    (x : GraphRealization P.geometry) : Measure (GraphContinuousPath P.geometry) :=
  P.physicalPathKernel hκ b hb x

instance GraphShiftedContactOperatorProblem.physicalPathLaw_probability
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (b : ℝ) (hb : 0 < b)
    (x : GraphRealization P.geometry) : IsProbabilityMeasure (P.physicalPathLaw hκ b hb x) :=
  inferInstanceAs (IsProbabilityMeasure (P.physicalPathKernel hκ b hb x))

theorem GraphShiftedContactOperatorProblem.physicalPathLaw_eq_map
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (b : ℝ) (hb : 0 < b)
    (x : GraphRealization P.geometry) :
    P.physicalPathLaw hκ b hb x = (P.continuousPathLaw hκ x).map (P.geometry.physicalPath b hb) :=
  Kernel.map_apply _ (P.geometry.physicalPath_measurable b hb) x

theorem GraphShiftedContactOperatorProblem.physicalPathLaw_initial
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (b : ℝ) (hb : 0 < b)
    (x : GraphRealization P.geometry) : ∀ᵐ p ∂P.physicalPathLaw hκ b hb x, p 0 = x := by
  rw [P.physicalPathLaw_eq_map]
  apply (ae_map_iff (P.geometry.physicalPath_measurable b hb).aemeasurable
    (measurableSet_eq_fun (continuous_eval_const 0).measurable measurable_const)).mpr
  simpa only [P.geometry.physicalPath_zero] using P.continuousPathLaw_initial hκ x

theorem GraphShiftedContactOperatorProblem.physicalPathLaw_vertex_value_independent
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0) (b c : ℝ)
    (hb : 0 < b) (hc : 0 < c) (x : GraphRealization P.geometry) :
    P.physicalPathLaw hκ b hb x = P.physicalPathLaw hκ c hc x := by
  rw [P.physicalPathLaw_eq_map, P.physicalPathLaw_eq_map]
  apply Measure.map_congr
  filter_upwards [P.physicalInverseClock_vertex_value_independent hκ x] with p hp
  apply ContinuousMap.ext
  intro t
  exact congrArg p (hp b c hb hc t)

end TimeTraps.Analysis
