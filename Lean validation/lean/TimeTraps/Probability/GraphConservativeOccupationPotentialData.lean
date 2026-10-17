module

public import TimeTraps.Probability.GraphConservativeOccupationKacTriangle
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Finite-time potentials of the actual graph Feller semigroup as
continuous graph functions. Uniform-norm Bochner integration supplies the
literal scalar potential and its joint time/state continuity. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.occupationPotential
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (T : ℝ) : C(GraphRealization P.geometry, ℝ) :=
  ∫ r in 0..T, P.realizedFeller r.toNNReal f

theorem GraphShiftedContactOperatorProblem.occupationPotential_apply
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    (T : ℝ) (y : GraphRealization P.geometry) :
    P.occupationPotential f T y = ∫ r in 0..T, P.realizedFeller r.toNNReal f y :=
  ((ContinuousMap.evalCLM ℝ y).intervalIntegral_comp_comm
    (((P.realizedFeller_strong_continuous f).comp continuous_real_toNNReal).intervalIntegrable 0 T)).symm

theorem GraphShiftedContactOperatorProblem.occupationPotential_continuous
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ)) :
    Continuous (P.occupationPotential f) := by
  apply continuous_iff_continuousAt.mpr
  intro T
  exact (((P.realizedFeller_strong_continuous f).comp continuous_real_toNNReal).integral_hasStrictDerivAt
    0 T).hasDerivAt.continuousAt

theorem GraphShiftedContactOperatorProblem.occupationPotential_joint_continuous
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ)) :
    Continuous (fun p : ℝ × GraphRealization P.geometry => P.occupationPotential f p.1 p.2) :=
  continuous_eval.comp (((P.occupationPotential_continuous f).comp continuous_fst).prodMk continuous_snd)

theorem GraphShiftedContactOperatorProblem.occupationPotential_norm_le
    (P : GraphShiftedContactOperatorProblem V E) (f : C(GraphRealization P.geometry, ℝ))
    {T : ℝ} (hT : 0 ≤ T) : ‖P.occupationPotential f T‖ ≤ T * ‖f‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := T) (fun r _ => P.realizedFeller_norm_le r.toNNReal f)
  simpa only [occupationPotential, sub_zero, abs_of_nonneg hT, mul_comm] using h

theorem GraphShiftedContactOperatorProblem.occupationPotential_sub
    (P : GraphShiftedContactOperatorProblem V E) (f g : C(GraphRealization P.geometry, ℝ)) (T : ℝ) :
    P.occupationPotential (f - g) T = P.occupationPotential f T - P.occupationPotential g T := by
  unfold occupationPotential
  simp only [map_sub]
  exact intervalIntegral.integral_sub
    (((P.realizedFeller_strong_continuous f).comp continuous_real_toNNReal).intervalIntegrable 0 T)
    (((P.realizedFeller_strong_continuous g).comp continuous_real_toNNReal).intervalIntegrable 0 T)

end TimeTraps.Analysis
