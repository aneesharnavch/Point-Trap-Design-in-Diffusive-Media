module

public import TimeTraps.Probability.GraphPhysicalTransitionData
public import TimeTraps.Probability.GraphPhysicalSpeedMeasure
public import TimeTraps.Probability.BoundedContinuousLaplaceUniqueness

@[expose] public section

/-! Pairings of the actual physical transition against the original
speed measure. Continuity and uniform bounds allow the previously
proved Laplace uniqueness theorem to recover individual-time symmetry. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.physicalTransitionPairing
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (f g : C(GraphRealization P.geometry, ℝ)) (t : ℝ≥0) : ℝ :=
  ∫ x, f x * P.physicalTransitionExpectation h0 b hb t g x ∂P.geometry.physicalSpeedMeasure

theorem GraphShiftedContactOperatorProblem.physicalTransitionPairing_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (f g : C(GraphRealization P.geometry, ℝ)) (t : ℝ≥0) :
    Integrable (fun x => f x * P.physicalTransitionExpectation h0 b hb t g x) P.geometry.physicalSpeedMeasure := by
  apply (integrable_const (‖f‖ * ‖g‖)).mono'
    (f.continuous.measurable.mul
      (P.physicalTransitionExpectation_measurable h0 b hb t g.continuous.measurable)).aestronglyMeasurable
  apply Eventually.of_forall
  intro x
  change ‖f x * P.physicalTransitionExpectation h0 b hb t g x‖ ≤ ‖f‖ * ‖g‖
  rw [norm_mul]
  exact mul_le_mul (f.norm_coe_le_norm x)
    (P.physicalTransitionExpectation_bound h0 b hb t g.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)

theorem GraphShiftedContactOperatorProblem.physicalTransitionPairing_continuous
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (f g : C(GraphRealization P.geometry, ℝ)) :
    Continuous (P.physicalTransitionPairing h0 b hb f g) := by
  apply continuous_of_dominated
    (fun t => (P.physicalTransitionPairing_integrable h0 b hb f g t).aestronglyMeasurable)
    (fun t => Eventually.of_forall (fun x => ?_)) (integrable_const (‖f‖ * ‖g‖))
    (Eventually.of_forall (fun x =>
      (P.physicalTransitionExpectation_continuous_time h0 b hb g x).const_mul (f x)))
  change ‖f x * P.physicalTransitionExpectation h0 b hb t g x‖ ≤ ‖f‖ * ‖g‖
  rw [norm_mul]
  exact mul_le_mul (f.norm_coe_le_norm x)
    (P.physicalTransitionExpectation_bound h0 b hb t g.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)

theorem GraphShiftedContactOperatorProblem.physicalTransitionPairing_bound
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (f g : C(GraphRealization P.geometry, ℝ)) (t : ℝ≥0) :
    ‖P.physicalTransitionPairing h0 b hb f g t‖ ≤
      (‖f‖ * ‖g‖) * P.geometry.physicalSpeedMeasure.real univ := by
  apply norm_integral_le_of_norm_le_const
  apply Eventually.of_forall
  intro x
  change ‖f x * P.physicalTransitionExpectation h0 b hb t g x‖ ≤ ‖f‖ * ‖g‖
  rw [norm_mul]
  exact mul_le_mul (f.norm_coe_le_norm x)
    (P.physicalTransitionExpectation_bound h0 b hb t g.norm_coe_le_norm x) (norm_nonneg _) (norm_nonneg _)

theorem GraphShiftedContactOperatorProblem.physicalTransitionPairing_eq_of_laplace
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (f g : C(GraphRealization P.geometry, ℝ))
    (heq : ∀ α : ℝ, 0 < α →
      (∫ r in Ioi (0 : ℝ), Real.exp (-α * r) * P.physicalTransitionPairing h0 b hb f g r.toNNReal) =
        ∫ r in Ioi (0 : ℝ), Real.exp (-α * r) * P.physicalTransitionPairing h0 b hb g f r.toNNReal) :
    P.physicalTransitionPairing h0 b hb f g = P.physicalTransitionPairing h0 b hb g f :=
  boundedContinuous_nonnegativeTime_laplace_unique
    (P.physicalTransitionPairing_continuous h0 b hb f g)
    (P.physicalTransitionPairing_continuous h0 b hb g f)
    (P.physicalTransitionPairing_bound h0 b hb f g)
    (P.physicalTransitionPairing_bound h0 b hb g f) heq

end TimeTraps.Analysis
