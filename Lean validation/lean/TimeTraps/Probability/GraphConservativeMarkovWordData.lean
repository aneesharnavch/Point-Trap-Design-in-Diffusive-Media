module

public import TimeTraps.Probability.GraphConservativeStrongMarkov
public import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

@[expose] public section

/-! Finite continuous future observations along the literal graph path
and their original iterated Feller kernels. Zero durations are retained. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E]

abbrev GraphMarkovWord (G : MetricGraph V E) := List (ℝ≥0 × C(GraphRealization G, ℝ))

noncomputable def graphMarkovCylinder (G : MetricGraph V E) :
    GraphMarkovWord G → ℝ≥0 → GraphContinuousPath G → ℝ
  | [], _, _ => 1
  | (h, f) :: w, t, p => f (p (t + h)) * graphMarkovCylinder G w (t + h) p

noncomputable def GraphShiftedContactOperatorProblem.markovCylinderKernel [Nonempty E]
    (P : GraphShiftedContactOperatorProblem V E) : GraphMarkovWord P.geometry → C(GraphRealization P.geometry, ℝ)
  | [] => 1
  | (h, f) :: w => P.realizedFeller h (f * P.markovCylinderKernel w)

noncomputable def graphMarkovCylinderBound {G : MetricGraph V E} : GraphMarkovWord G → ℝ
  | [] => 1
  | (_, f) :: w => ‖f‖ * graphMarkovCylinderBound w

omit [Fintype V] in
theorem graphMarkovCylinderBound_nonneg {G : MetricGraph V E} (w : GraphMarkovWord G) :
    0 ≤ graphMarkovCylinderBound w := by
  induction w with
  | nil => exact zero_le_one
  | cons a w ih => exact mul_nonneg (norm_nonneg a.2) ih

omit [Fintype V] in
theorem graphMarkovCylinder_bound (G : MetricGraph V E) (w : GraphMarkovWord G)
    (t : ℝ≥0) (p : GraphContinuousPath G) :
    ‖graphMarkovCylinder G w t p‖ ≤ graphMarkovCylinderBound w := by
  induction w generalizing t with
  | nil => exact le_of_eq norm_one
  | cons a w ih =>
      rcases a with ⟨h, f⟩
      change ‖f (p (t + h)) * graphMarkovCylinder G w (t + h) p‖ ≤ ‖f‖ * graphMarkovCylinderBound w
      rw [norm_mul]
      exact mul_le_mul (f.norm_coe_le_norm _) (ih _) (norm_nonneg _) (norm_nonneg _)

theorem GraphShiftedContactOperatorProblem.markovCylinderKernel_bound [Nonempty E]
    (P : GraphShiftedContactOperatorProblem V E) (w : GraphMarkovWord P.geometry) :
    ‖P.markovCylinderKernel w‖ ≤ graphMarkovCylinderBound w := by
  induction w with
  | nil =>
      apply (ContinuousMap.norm_le _ zero_le_one).mpr
      intro z
      exact le_of_eq norm_one
  | cons a w ih =>
      rcases a with ⟨h, f⟩
      exact (P.realizedFeller_norm_le h _).trans
        ((norm_mul_le f _).trans (mul_le_mul_of_nonneg_left ih (norm_nonneg f)))

theorem graphMarkovCylinder_stopped_stronglyMeasurable (G : MetricGraph V E) (w : GraphMarkovWord G)
    {τ : GraphContinuousPath G → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration G) (fun p => (τ p : WithTop ℝ≥0))) :
    StronglyMeasurable (fun p => graphMarkovCylinder G w (τ p) p) := by
  induction w generalizing τ with
  | nil => exact stronglyMeasurable_const
  | cons a w ih =>
      rcases a with ⟨h, f⟩
      have hσ := finiteStoppingTime_add hτ h
      exact ((continuousObservation_stopped_stronglyMeasurable
        (fun t (p : GraphContinuousPath G) => f (p t)) (graphObservation_stronglyAdapted G f)
        (fun p => f.continuous.comp p.continuous) hσ).mono hσ.measurableSpace_le).mul (ih hσ)

theorem GraphShiftedContactOperatorProblem.markovCylinder_stopped_integrable [Nonempty E]
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (w : GraphMarkovWord P.geometry)
    {τ : GraphContinuousPath P.geometry → ℝ≥0}
    (hτ : IsStoppingTime (graphContinuousNaturalFiltration P.geometry) (fun p => (τ p : WithTop ℝ≥0))) :
    Integrable (fun p => graphMarkovCylinder P.geometry w (τ p) p) (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  exact Integrable.of_bound (graphMarkovCylinder_stopped_stronglyMeasurable P.geometry w hτ).aestronglyMeasurable
    (graphMarkovCylinderBound w) (Eventually.of_forall (fun p => graphMarkovCylinder_bound P.geometry w _ p))

end TimeTraps.Analysis
