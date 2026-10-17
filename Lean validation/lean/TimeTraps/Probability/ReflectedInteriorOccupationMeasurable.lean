module

public import TimeTraps.Probability.ReflectedInteriorOccupationIdentity
public import Mathlib.MeasureTheory.Constructions.Polish.Basic

@[expose] public section

/-! Joint measurability of the actual periodized coefficient and of the
established folded occupation density. These facts permit a justified
exchange of the spatial and probability almost-everywhere quantifiers. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TimeTraps.Analysis
open scoped NNReal ENNReal

theorem affineBrownianRegulator_start_jointlyMeasurable (σ L : ℝ) (b : ℤ) (T : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => affineBrownianRegulator p.1 σ L b T p.2) := by
  unfold affineBrownianRegulator
  apply Measurable.tsum
  intro k
  have hφ : Measurable (fun p : ℝ × (ℕ → ℝ) =>
      (((((2 * k + b : ℤ) : ℝ) * L) - p.1) / σ, p.2)) := by fun_prop
  have hm := (brownianLocalTimeTimeField_timeSlice_measurable T).comp hφ
  exact measurable_const.mul hm

theorem reflectedInteriorOccupationCoefficient_jointlyMeasurable (x σ L : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => reflectedInteriorOccupationCoefficient x σ L p.1 T p.2) := by
  have hminus : Measurable (fun p : ℝ × (ℕ → ℝ) => (x - p.1, p.2)) := by fun_prop
  have hplus : Measurable (fun p : ℝ × (ℕ → ℝ) => (x + p.1, p.2)) := by fun_prop
  have hm := (affineBrownianRegulator_start_jointlyMeasurable σ L 0 T).comp hminus
  have hp := (affineBrownianRegulator_start_jointlyMeasurable σ L 0 T).comp hplus
  exact (hm.add hp).div_const (σ ^ 2)

theorem foldedOccupationDensity_timeSlice_jointlyMeasurable (L D x : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ × (ℕ → ℝ) => foldedOccupationDensity L D x T p.2 p.1) := by
  let G : ℝ × (ℕ → ℝ) → ℝ≥0∞ := fun p =>
    reflectedFoldDensity L (fun y => ENNReal.ofReal
      (affineBrownianOccupationDensity x (Real.sqrt (2 * D)) y T p.2)) p.1
  have hG : Measurable G := by
    unfold G reflectedFoldDensity
    apply Measurable.tsum
    intro k
    have hleft : Measurable (fun p : ℝ × (ℕ → ℝ) => (p.1 + (k : ℝ) * (2 * L), p.2)) := by fun_prop
    have hright : Measurable (fun p : ℝ × (ℕ → ℝ) => ((k : ℝ) * (2 * L) - p.1, p.2)) := by fun_prop
    have hl := (affineBrownianOccupationDensity_timeSlice_measurable x (Real.sqrt (2 * D)) T).comp hleft
    have hr := (affineBrownianOccupationDensity_timeSlice_measurable x (Real.sqrt (2 * D)) T).comp hright
    exact hl.ennreal_ofReal.add hr.ennreal_ofReal
  let A : Set (ℝ × (ℕ → ℝ)) := {p | p.1 ∈ Ioo 0 L}
  have hA : MeasurableSet A := measurableSet_Ioo.preimage measurable_fst
  change Measurable (fun p : ℝ × (ℕ → ℝ) => (A.indicator G p).toReal)
  exact (hG.indicator hA).ennreal_toReal

end TimeTraps.Probability
