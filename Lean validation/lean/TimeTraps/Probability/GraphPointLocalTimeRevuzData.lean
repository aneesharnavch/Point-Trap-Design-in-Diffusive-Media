module

public import TimeTraps.Probability.GraphPointLocalTimeContactIntegral
public import TimeTraps.Probability.GraphPointLocalTimeNormalization

@[expose] public section

/-! The literal canonical graph contact integral is an actual measurable
square-integrable path functional. Arbitrary spatial tests are allowed
because the proved contact measure evaluates them only at its target. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.pointLocalTimeContactIntegral
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) (p : GraphContinuousPath P.geometry) : ℝ :=
  ∫ t in Ioc (0 : ℝ) T.val, g (p t.toNNReal) ∂P.pointLocalTimeMeasure a p

theorem GraphShiftedContactOperatorProblem.pointLocalTimeContactIntegral_eq
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    P.pointLocalTimeContactIntegral a g T p = g a * P.pointLocalTimePath a p T :=
  (P.pointLocalTimeMeasure_contact a p g T).2

theorem GraphShiftedContactOperatorProblem.pointLocalTimeContactIntegral_measurable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) :
    Measurable (P.pointLocalTimeContactIntegral a g T) := by
  have he : P.pointLocalTimeContactIntegral a g T = fun p => g a * P.pointLocalTimePath a p T :=
    funext (P.pointLocalTimeContactIntegral_eq a g T)
  rw [he]
  exact measurable_const.mul ((continuous_eval_const T).measurable.comp (P.pointLocalTimePath_measurable a))

theorem GraphShiftedContactOperatorProblem.pointLocalTimeContactIntegral_memLp
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) :
    MemLp (P.pointLocalTimeContactIntegral a g T) 2 (P.continuousPathLaw hκ x) := by
  apply ((P.pointLocalTimePath_memLp hκ x a T).const_mul (g a)).ae_eq
  exact Eventually.of_forall (fun p => (P.pointLocalTimeContactIntegral_eq a g T p).symm)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeContactIntegral_mean
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) :
    (∫ p, P.pointLocalTimeContactIntegral a g T p ∂P.continuousPathLaw hκ x) =
      g a * P.realizedHeatPointPotential x a T := by
  calc
    _ = ∫ p, g a * P.pointLocalTimePath a p T ∂P.continuousPathLaw hκ x :=
      integral_congr_ae (Eventually.of_forall (P.pointLocalTimeContactIntegral_eq a g T))
    _ = _ := by rw [integral_const_mul, P.pointLocalTimePath_mean hκ x a T]

end TimeTraps.Analysis
