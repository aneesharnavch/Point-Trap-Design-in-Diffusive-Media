module

public import TimeTraps.Probability.GraphPhysicalClockLaplaceStartBound
public import TimeTraps.Probability.BoundedContinuousLaplaceUniqueness

@[expose] public section

/-! Initial-point Fubini for the genuine clock Laplace expression.
The uniform positive clock speed yields product absolute integrability;
the final identity uses the original rho-weighted length measure. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalClockLaplaceIntegrand_initial_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) {α : ℝ} (hα : 0 < α)
    (f g : C(GraphRealization P.geometry, ℝ)) :
    Integrable (fun q : ℝ × GraphRealization P.geometry =>
      f q.2 * P.physicalClockLaplaceIntegrand h0 b hb α g q.1 q.2)
        ((volume.restrict (Ioi (0 : ℝ))).prod P.geometry.physicalSpeedMeasure) := by
  have hm := (f.continuous.measurable.comp measurable_snd).mul
    (P.physicalClockLaplaceIntegrand_jointlyMeasurable h0 b hb α g.continuous.measurable)
  have hrate : 0 < α * (P.geometry.physicalSpeedLower b hb : ℝ) :=
    mul_pos hα (P.geometry.physicalSpeedLower_pos b hb)
  have hd := ((exp_neg_integrableOn_Ioi 0 hrate).const_mul
    (‖f‖ * (P.geometry.physicalSpeedUpper b hb : ℝ) * ‖g‖)).comp_fst
      P.geometry.physicalSpeedMeasure
  apply hd.mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro q
  change ‖f q.2 * P.physicalClockLaplaceIntegrand h0 b hb α g q.1 q.2‖ ≤
    (‖f‖ * (P.geometry.physicalSpeedUpper b hb : ℝ) * ‖g‖) *
      Real.exp (-(α * (P.geometry.physicalSpeedLower b hb : ℝ)) * q.1)
  rw [norm_mul]
  have he := mul_le_mul (f.norm_coe_le_norm q.2)
    (P.physicalClockLaplaceIntegrand_bound h0 b hb hα.le g q.1 q.2)
    (norm_nonneg _) (norm_nonneg f)
  exact he.trans_eq (by ring)

theorem GraphShiftedContactOperatorProblem.physicalClockLaplaceIntegrand_initial_swap
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) {α : ℝ} (hα : 0 < α)
    (f g : C(GraphRealization P.geometry, ℝ)) :
    (∫ x, f x * (∫ r in Ioi (0 : ℝ), P.physicalClockLaplaceIntegrand h0 b hb α g r x)
      ∂P.geometry.physicalSpeedMeasure) =
      ∫ r in Ioi (0 : ℝ), ∫ x,
        P.geometry.physicalSpeed b x * f x * P.physicalClockLaplaceIntegrand h0 b hb α g r x
          ∂P.geometry.lengthMeasure := by
  have hi := P.physicalClockLaplaceIntegrand_initial_integrable h0 b hb hα f g
  calc
    _ = ∫ x, (∫ r in Ioi (0 : ℝ), f x * P.physicalClockLaplaceIntegrand h0 b hb α g r x)
        ∂P.geometry.physicalSpeedMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by
        dsimp only
        exact (integral_const_mul _ _).symm)
    _ = ∫ r in Ioi (0 : ℝ), ∫ x, f x * P.physicalClockLaplaceIntegrand h0 b hb α g r x
        ∂P.geometry.physicalSpeedMeasure := (integral_integral_swap hi).symm
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro r
      dsimp only
      rw [P.geometry.physicalSpeedMeasure_integral b hb]
      apply integral_congr_ae
      exact Eventually.of_forall (fun x => by ring)

end TimeTraps.Analysis
