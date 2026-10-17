module

public import TimeTraps.Analysis.ReversibleResistanceCoordinateTimeSubstitution
public import TimeTraps.Probability.ReversibleResistanceTimeChangePaths

@[expose] public section

/-! Substitution at the actual inverse clock on one Brownian regular
event, simultaneously for all horizons and all real time tests. These
are identities for the literal time integrals of the constructed process. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal

theorem reflectedPositiveTimeInversePath_integral_substitution
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (g : ℝ≥0 → ℝ) (T : ℝ≥0) :
    (∫ t in (0 : ℝ)..T.val,
      g (reflectedPositiveTimeInversePath L D x c t.toNNReal ω)) =
      ∫ s in (0 : ℝ)..(reflectedPositiveTimeInversePath L D x c T ω).val,
        g s.toNNReal * c (foldedTrajectory L D x brownianDyadicPath s.toNNReal ω) := by
  simp only [reflectedPositiveTimeInversePath, if_pos hω]
  have he := reflectedPositiveTimeInverse_eq L hL D x brownianDyadicPath
    c hc hpos ω hω.continuous
  have hi := (reflectedPositiveTimeSpeed L hL D x brownianDyadicPath
    c hc hpos ω hω.continuous).inverse_integral_substitution g T
  simpa only [← he, reflectedPositiveTimeSpeed_rate] using hi

theorem reflectedPositiveTimeInversePath_integral_reciprocal
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {ω : ℕ → ℝ} (hω : BrownianDyadicRegular ω) (g : ℝ≥0 → ℝ) (T : ℝ≥0) :
    (∫ s in (0 : ℝ)..(reflectedPositiveTimeInversePath L D x c T ω).val, g s.toNNReal) =
      ∫ t in (0 : ℝ)..T.val,
        g (reflectedPositiveTimeInversePath L D x c t.toNNReal ω) /
          c (foldedTrajectory L D x brownianDyadicPath
            (reflectedPositiveTimeInversePath L D x c t.toNNReal ω) ω) := by
  have hi := reflectedPositiveTimeInversePath_integral_substitution L hL D x c hc hpos hω
    (fun s => g s / c (foldedTrajectory L D x brownianDyadicPath s ω)) T
  simpa only [div_mul_cancel₀ _ (hpos _ (foldedTrajectory_mem L hL D x brownianDyadicPath _ ω)).ne']
    using hi.symm

theorem reversibleResistancePath_integral_substitution (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (g : ℝ → ℝ) (T : ℝ≥0),
      (∫ t in (0 : ℝ)..T.val, g (reversibleResistancePath A x t.toNNReal ω)) =
        ∫ s in (0 : ℝ)..(reversibleResistanceInversePath A x T ω).val,
          g (A.resistanceInverse (reversibleResistanceReference A x s.toNNReal ω)) *
            A.resistanceSpeed (reversibleResistanceReference A x s.toNNReal ω) := by
  filter_upwards [brownianDyadic_regular_ae] with ω hω
  intro g T
  exact reflectedPositiveTimeInversePath_integral_substitution A.resistanceLength
    A.resistanceLength_pos 1 (A.resistance x) A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y) hω
        (fun s => g (A.resistanceInverse (reversibleResistanceReference A x s ω))) T

theorem reversibleResistancePath_integral_reciprocal (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (g : ℝ → ℝ) (T : ℝ≥0),
      (∫ s in (0 : ℝ)..(reversibleResistanceInversePath A x T ω).val,
        g (A.resistanceInverse (reversibleResistanceReference A x s.toNNReal ω))) =
        ∫ t in (0 : ℝ)..T.val, g (reversibleResistancePath A x t.toNNReal ω) /
          (A.conductance (reversibleResistancePath A x t.toNNReal ω) *
            A.source.density (reversibleResistancePath A x t.toNNReal ω)) := by
  filter_upwards [brownianDyadic_regular_ae] with ω hω
  intro g T
  exact reflectedPositiveTimeInversePath_integral_reciprocal A.resistanceLength
    A.resistanceLength_pos 1 (A.resistance x) A.resistanceSpeed
      A.resistanceSpeed_continuous.continuousOn (fun y _ => A.resistanceSpeed_pos y) hω
        (fun s => g (A.resistanceInverse (reversibleResistanceReference A x s ω))) T

end TimeTraps.Probability
