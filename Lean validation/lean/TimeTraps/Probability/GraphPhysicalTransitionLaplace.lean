module

public import TimeTraps.Probability.GraphPhysicalTransitionPairing

@[expose] public section

/-! Discounted physical transition pairings satisfy genuine Fubini.
The exponential probability bound supplies product integrability on
the entire half-line; no reversible law is used in this step. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.physicalTransitionPairing_laplace_joint_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (f g : C(GraphRealization P.geometry, ℝ)) {α : ℝ} (hα : 0 < α) :
    Integrable (fun q : ℝ × GraphRealization P.geometry =>
      Real.exp (-α * q.1) * (f q.2 * P.physicalTransitionExpectation h0 b hb q.1.toNNReal g q.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod P.geometry.physicalSpeedMeasure) := by
  have hp : Measurable (fun q : ℝ × GraphRealization P.geometry => (q.1.toNNReal, q.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have hm0 := (P.physicalTransitionExpectation_jointlyMeasurable h0 b hb g).comp hp
  have he : ((fun q : ℝ≥0 × GraphRealization P.geometry =>
      P.physicalTransitionExpectation h0 b hb q.1 g q.2) ∘ fun q : ℝ × GraphRealization P.geometry => (q.1.toNNReal, q.2)) =
      (fun q : ℝ × GraphRealization P.geometry => P.physicalTransitionExpectation h0 b hb q.1.toNNReal g q.2) := rfl
  rw [he] at hm0
  have hmexp : Measurable (fun q : ℝ × GraphRealization P.geometry => Real.exp (-α * q.1)) := by fun_prop
  have hm := hmexp.mul ((f.continuous.measurable.comp measurable_snd).mul hm0)
  have hd := ((exp_neg_integrableOn_Ioi 0 hα).mul_const (‖f‖ * ‖g‖)).comp_fst P.geometry.physicalSpeedMeasure
  apply hd.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro q
  change ‖Real.exp (-α * q.1) * (f q.2 * P.physicalTransitionExpectation h0 b hb q.1.toNNReal g q.2)‖ ≤
    Real.exp (-α * q.1) * (‖f‖ * ‖g‖)
  rw [norm_mul, Real.norm_of_nonneg (Real.exp_pos _).le, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  exact mul_le_mul (f.norm_coe_le_norm q.2)
    (P.physicalTransitionExpectation_bound h0 b hb q.1.toNNReal g.norm_coe_le_norm q.2)
    (norm_nonneg _) (norm_nonneg _)

theorem GraphShiftedContactOperatorProblem.physicalTransitionPairing_laplace_swap
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (f g : C(GraphRealization P.geometry, ℝ)) {α : ℝ} (hα : 0 < α) :
    (∫ r in Ioi (0 : ℝ), Real.exp (-α * r) * P.physicalTransitionPairing h0 b hb f g r.toNNReal) =
      ∫ x, f x * (∫ r in Ioi (0 : ℝ), Real.exp (-α * r) *
        P.physicalTransitionExpectation h0 b hb r.toNNReal g x) ∂P.geometry.physicalSpeedMeasure := by
  have hj : Integrable (Function.uncurry (fun (r : ℝ) (x : GraphRealization P.geometry) =>
      Real.exp (-α * r) * (f x * P.physicalTransitionExpectation h0 b hb r.toNNReal g x)))
      ((volume.restrict (Ioi (0 : ℝ))).prod P.geometry.physicalSpeedMeasure) :=
    P.physicalTransitionPairing_laplace_joint_integrable h0 b hb f g hα
  have h := integral_integral_swap hj
  have hr (r : ℝ) : (∫ x, Real.exp (-α * r) *
      (f x * P.physicalTransitionExpectation h0 b hb r.toNNReal g x) ∂P.geometry.physicalSpeedMeasure) =
      Real.exp (-α * r) * P.physicalTransitionPairing h0 b hb f g r.toNNReal :=
    integral_const_mul _ _
  have hx (x : GraphRealization P.geometry) :
      (∫ r in Ioi (0 : ℝ), Real.exp (-α * r) *
        (f x * P.physicalTransitionExpectation h0 b hb r.toNNReal g x)) =
      f x * (∫ r in Ioi (0 : ℝ), Real.exp (-α * r) * P.physicalTransitionExpectation h0 b hb r.toNNReal g x) := by
    simp only [← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall (fun r => by ring)
  simpa only [hr, hx] using h

end TimeTraps.Analysis
