module

public import TimeTraps.Analysis.GraphContactRealizedHeatIntegral
public import Mathlib.Probability.Kernel.Composition.Comp
public import Mathlib.Probability.Kernel.WithDensity

@[expose] public section

/-! The genuine subprobability kernel on the original compact graph for
variable conductance and nonnegative reactions with one positive contact.
Its density is the same heat kernel against ordinary physical edge length. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphContactOperatorProblem.realizedHeatTransition
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t) :
    Kernel (GraphRealization P.geometry) (GraphRealization P.geometry) :=
  (Kernel.const _ P.geometry.lengthMeasure).withDensity
    (fun x y => ENNReal.ofReal (P.realizedHeatKernel t ht x y))

theorem GraphContactOperatorProblem.realizedHeatTransition_apply
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) :
    P.realizedHeatTransition t ht x = P.geometry.lengthMeasure.withDensity
      (fun y => ENNReal.ofReal (P.realizedHeatKernel t ht x y)) :=
  Kernel.withDensity_apply _ (P.realizedHeatKernel_measurable t ht).ennreal_ofReal x

theorem GraphContactOperatorProblem.realizedHeatTransition_mass
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) :
    P.realizedHeatTransition t ht x univ =
      ENNReal.ofReal (P.realizedHeatEvaluation t ht x
        (graphSobolevSpaceStateL P.geometry P.operatorOne)) := by
  rw [P.realizedHeatTransition_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  calc
    _ = ENNReal.ofReal (∫ y, P.realizedHeatKernel t ht x y ∂P.geometry.lengthMeasure) :=
      (ofReal_integral_eq_lintegral_ofReal (P.realizedHeatKernel_integrable t ht x)
        (Eventually.of_forall (P.realizedHeatKernel_nonneg t ht x))).symm
    _ = _ := congrArg ENNReal.ofReal (P.realizedHeatKernel_mass t ht x)

theorem GraphContactOperatorProblem.realizedHeatTransition_mass_le_one
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) : P.realizedHeatTransition t ht x univ ≤ 1 := by
  rw [P.realizedHeatTransition_mass, ← P.realizedHeatKernel_mass, ← ENNReal.ofReal_one]
  exact ENNReal.ofReal_le_ofReal (P.realizedHeatKernel_mass_bounds t ht x).2

instance GraphContactOperatorProblem.realizedHeatTransition_finite
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t) :
    IsFiniteKernel (P.realizedHeatTransition t ht) where
  exists_univ_le := ⟨1, ENNReal.one_lt_top, P.realizedHeatTransition_mass_le_one t ht⟩

theorem GraphContactOperatorProblem.realizedHeatTransition_integral
    (P : GraphContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ) :
    (∫ y, f y ∂P.realizedHeatTransition t ht x) =
      ∫ y, P.realizedHeatKernel t ht x y * f y ∂P.geometry.lengthMeasure := by
  rw [P.realizedHeatTransition_apply,
    integral_withDensity_eq_integral_toReal_smul
      (P.realizedHeatKernel_measurable t ht).of_uncurry_left.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    change (ENNReal.ofReal (P.realizedHeatKernel t ht x y)).toReal * f y = _
    rw [ENNReal.toReal_ofReal (P.realizedHeatKernel_nonneg t ht x y)])

end TimeTraps.Analysis
