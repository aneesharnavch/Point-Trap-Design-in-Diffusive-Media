module

public import TimeTraps.Probability.GraphConservativeOccupationPotential
public import TimeTraps.Probability.GraphConservativeContinuousMarginal

@[expose] public section

/-! The true first occupation moment equals the finite-time graph
potential. Joint bounded integrability is proved before interchanging the
sample expectation with ordinary time integration. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.occupation_joint_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ) :
    Integrable (fun q : ℝ × GraphContinuousPath P.geometry => f (q.2 q.1.toNNReal))
      ((volume.restrict (uIoc 0 T)).prod (P.continuousPathLaw hκ x)) := by
  let inst := P.continuousPathLaw_probability hκ x
  let instTime : IsFiniteMeasure (volume.restrict (uIoc 0 T)) := by
    change IsFiniteMeasure (volume.restrict (Ioc (min 0 T) (max 0 T)))
    infer_instance
  have hm : Measurable (fun q : ℝ × GraphContinuousPath P.geometry => f (q.2 q.1.toNNReal)) := by fun_prop
  exact (integrable_const ‖f‖).mono' hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun q => f.norm_coe_le_norm _))

theorem GraphShiftedContactOperatorProblem.occupation_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ))
    {T : ℝ} (hT : 0 ≤ T) :
    Integrable (fun p : GraphContinuousPath P.geometry => ∫ s in 0..T, f (p s.toNNReal))
      (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  have h := (P.occupation_joint_integrable hκ x f T).integral_prod_right
  simpa only [uIoc_of_le hT, intervalIntegral.integral_of_le hT] using h

theorem GraphShiftedContactOperatorProblem.occupation_mean_potential
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) (T : ℝ) :
    (∫ p : GraphContinuousPath P.geometry, (∫ s in 0..T, f (p s.toNNReal))
      ∂P.continuousPathLaw hκ x) = P.occupationPotential f T x := by
  let inst := P.continuousPathLaw_probability hκ x
  calc
    _ = ∫ s in 0..T, ∫ p : GraphContinuousPath P.geometry, f (p s.toNNReal)
        ∂P.continuousPathLaw hκ x :=
      (intervalIntegral_integral_swap (P.occupation_joint_integrable hκ x f T)).symm
    _ = ∫ s in 0..T, P.realizedFeller s.toNNReal f x := by
      apply intervalIntegral.integral_congr
      intro s _
      exact P.continuousPathLaw_observation_integral hκ x s.toNNReal f
    _ = _ := (P.occupationPotential_apply f T x).symm

end TimeTraps.Analysis
