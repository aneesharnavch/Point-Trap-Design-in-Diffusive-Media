module

public import TimeTraps.Probability.GraphPhysicalClockLaplaceTransition
public import TimeTraps.Probability.GraphPhysicalClockLaplaceStartIntegral
public import TimeTraps.Probability.GraphPhysicalTransitionLaplace

@[expose] public section

/-! The actual physical pairing Laplace transform is the integrated
original reference-clock correlation. Symmetry of that correlation is
a sufficient condition here; the stationary path reversal discharges it. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.physicalTransitionPairing_laplace_clock
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (f g : C(GraphRealization P.geometry, ℝ)) {α : ℝ} (hα : 0 < α) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
      P.physicalTransitionPairing h0 b hb f g t.toNNReal) =
      ∫ r in Ioi (0 : ℝ), ∫ x, P.geometry.physicalSpeed b x * f x *
        P.physicalClockLaplaceIntegrand h0 b hb α g r x ∂P.geometry.lengthMeasure := by
  rw [P.physicalTransitionPairing_laplace_swap h0 b hb f g hα]
  calc
    _ = ∫ x, f x * (∫ r in Ioi (0 : ℝ),
        P.physicalClockLaplaceIntegrand h0 b hb α g r x)
          ∂P.geometry.physicalSpeedMeasure := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      dsimp only
      rw [P.physicalTransitionExpectation_laplace_integrand h0 b hb x
        g.continuous.measurable g.norm_coe_le_norm hα]
    _ = _ := P.physicalClockLaplaceIntegrand_initial_swap h0 b hb hα f g

theorem GraphShiftedContactOperatorProblem.physicalTransitionPairing_eq_of_clock_symmetry
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (b : ℝ) (hb : 0 < b) (f g : C(GraphRealization P.geometry, ℝ))
    (hs : ∀ α : ℝ, 0 < α → ∀ r : ℝ,
      (∫ x, P.geometry.physicalSpeed b x * f x *
        P.physicalClockLaplaceIntegrand h0 b hb α g r x ∂P.geometry.lengthMeasure) =
      ∫ x, P.geometry.physicalSpeed b x * g x *
        P.physicalClockLaplaceIntegrand h0 b hb α f r x ∂P.geometry.lengthMeasure) :
    P.physicalTransitionPairing h0 b hb f g = P.physicalTransitionPairing h0 b hb g f := by
  apply P.physicalTransitionPairing_eq_of_laplace h0 b hb f g
  intro α hα
  rw [P.physicalTransitionPairing_laplace_clock h0 b hb f g hα,
    P.physicalTransitionPairing_laplace_clock h0 b hb g f hα]
  exact integral_congr_ae (Eventually.of_forall (hs α hα))

end TimeTraps.Analysis
