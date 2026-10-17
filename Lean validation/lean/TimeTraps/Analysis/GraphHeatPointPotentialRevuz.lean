module

public import TimeTraps.Analysis.GraphHeatPointPotentialSemigroup
public import TimeTraps.Analysis.GraphHeatPointPotentialJoint
public import TimeTraps.Analysis.ReflectedAtomicRevuzAverage

@[expose] public section

/-! The genuine graph point potential has unit-atom normalization
relative to ordinary edge length. Symmetry transports the source test
to the actual Feller semigroup, including at every vertex. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_source_integrable
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (a : GraphRealization P.geometry) (T : ℝ) :
    Integrable (fun x => f x * P.realizedHeatPointPotential x a T) P.geometry.lengthMeasure := by
  have hp := P.realizedHeatPointPotential_joint_continuous.comp
      (show Continuous (fun x : GraphRealization P.geometry => ((x, a), T)) from
        (continuous_id.prodMk continuous_const).prodMk continuous_const)
  have hc := f.continuous.mul hp
  exact hc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_source_pairing
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (a : GraphRealization P.geometry) {T : ℝ} (hT : 0 ≤ T) :
    (∫ x, f x * P.realizedHeatPointPotential x a T ∂P.geometry.lengthMeasure) =
      P.occupationPotential f T a := by
  rw [P.occupationPotential_pointPotential f a hT]
  apply integral_congr_ae
  apply Eventually.of_forall
  intro x
  dsimp only
  rw [P.realizedHeatPointPotential_symmetric x a T, mul_comm]

theorem GraphShiftedContactOperatorProblem.realizedHeatPointPotential_source_shortTime
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (a : GraphRealization P.geometry) :
    Tendsto (fun t : ℝ => t⁻¹ * ∫ x, f x * P.realizedHeatPointPotential x a t ∂P.geometry.lengthMeasure)
      (𝓝[>] 0) (𝓝 (f a)) := by
  have hc : Continuous (fun s : ℝ => P.realizedFeller s.toNNReal f a) :=
    ((continuous_eval_const a).comp (P.realizedFeller_strong_continuous f)).comp continuous_real_toNNReal
  have ht := reflectedAtomicRevuz_continuous_average hc
  simp only [Real.toNNReal_zero, P.realizedFeller_zero, ContinuousLinearMap.id_apply] at ht
  apply ht.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  rw [P.realizedHeatPointPotential_source_pairing f a (le_of_lt ht), P.occupationPotential_apply]

end TimeTraps.Analysis
