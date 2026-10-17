module

public import TimeTraps.Probability.GraphPointLocalTimeL2Properties
public import TimeTraps.Analysis.GraphHeatPointPotentialRevuz

@[expose] public section

/-! The actual graph point-local-time L2 limits have unit-atom mean
normalization relative to ordinary length, including at vertices. The
literal contact-integral version follows after canonical pathwise
realization and support are identified; neither is assumed here. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_mean_continuous
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (a : GraphRealization P.geometry) (T : ℝ≥0) :
    Continuous (fun x => ∫ p, P.pointLocalTimeL2 hκ x a T p ∂P.continuousPathLaw hκ x) := by
  simp_rw [P.pointLocalTimeL2_mean hκ]
  have hc := P.realizedHeatPointPotential_joint_continuous.comp
    (show Continuous (fun x : GraphRealization P.geometry => ((x, a), (T : ℝ))) from
      (continuous_id.prodMk continuous_const).prodMk continuous_const)
  exact hc

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_weightedMean_integrable
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (a : GraphRealization P.geometry) (T : ℝ≥0) (f : C(GraphRealization P.geometry, ℝ)) :
    Integrable (fun x => f x * ∫ p, P.pointLocalTimeL2 hκ x a T p ∂P.continuousPathLaw hκ x)
      P.geometry.lengthMeasure := by
  simp_rw [P.pointLocalTimeL2_mean hκ]
  exact P.realizedHeatPointPotential_source_integrable f a T

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_length_pairing
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (a : GraphRealization P.geometry) (T : ℝ≥0) (f : C(GraphRealization P.geometry, ℝ)) :
    (∫ x, f x * (∫ p, P.pointLocalTimeL2 hκ x a T p ∂P.continuousPathLaw hκ x)
      ∂P.geometry.lengthMeasure) = P.occupationPotential f T a := by
  simp_rw [P.pointLocalTimeL2_mean hκ]
  exact P.realizedHeatPointPotential_source_pairing f a T.coe_nonneg

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_length_shortTime
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (a : GraphRealization P.geometry) (f : C(GraphRealization P.geometry, ℝ)) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ x, f x *
      (∫ p, P.pointLocalTimeL2 hκ x a t.toNNReal p ∂P.continuousPathLaw hκ x)
        ∂P.geometry.lengthMeasure) (𝓝[>] 0) (𝓝 (f a)) := by
  apply (P.realizedHeatPointPotential_source_shortTime f a).congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp_rw [P.pointLocalTimeL2_mean hκ]
  rw [Real.coe_toNNReal t (le_of_lt ht)]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeL2_length_mass
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (a : GraphRealization P.geometry) (T : ℝ≥0) :
    (∫ x, (∫ p, P.pointLocalTimeL2 hκ x a T p ∂P.continuousPathLaw hκ x)
      ∂P.geometry.lengthMeasure) = T.val := by
  calc
    _ = ∫ x, P.realizedHeatPointPotential x a (T : ℝ) ∂P.geometry.lengthMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => P.pointLocalTimeL2_mean hκ x a T)
    _ = P.occupationPotential (ContinuousMap.const _ (1 : ℝ)) (T : ℝ) a := by
      simpa only [ContinuousMap.const_apply, one_mul] using
        P.realizedHeatPointPotential_source_pairing (ContinuousMap.const _ (1 : ℝ)) a T.coe_nonneg
    _ = T.val := by
      rw [P.occupationPotential_apply]
      simp only [P.realizedFeller_one hκ, ContinuousMap.const_apply,
        intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_one]
      rfl

end TimeTraps.Analysis
