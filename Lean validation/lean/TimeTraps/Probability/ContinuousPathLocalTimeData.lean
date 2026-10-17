module

public import TimeTraps.Probability.ContinuousPathOccupationBand
public import Mathlib.MeasureTheory.Constructions.Polish.StronglyMeasurable

@[expose] public section

/-! A canonical Borel continuous-path local-time functional, constructed
as the compact-open limit of literal shrinking occupation bands. The
good-path condition records convergence, rather than additivity. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory Filter
open scoped NNReal Topology

def occupationBandRadius (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem occupationBandRadius_pos (n : ℕ) : 0 < occupationBandRadius n := by
  unfold occupationBandRadius
  positivity

theorem occupationBandRadius_tendsto : Tendsto occupationBandRadius atTop (𝓝[>] (0 : ℝ)) :=
  tendsto_nhdsWithin_iff.mpr
    ⟨tendsto_one_div_add_atTop_nhds_zero_nat, Eventually.of_forall occupationBandRadius_pos⟩

def HasContinuousOccupationLocalTime (a : ℝ) (m : ℝ → ℝ) (p : ReversibleNeumannFullPath) : Prop :=
  ∃ l : ReversibleNeumannFullPath, Tendsto
    (fun n => continuousPathOccupationBand a (occupationBandRadius n) (m (occupationBandRadius n)) p)
      atTop (𝓝 l)

def continuousPathLocalTime (a : ℝ) (m : ℝ → ℝ) (p : ReversibleNeumannFullPath) :
    ReversibleNeumannFullPath :=
  limUnder atTop (fun n =>
    continuousPathOccupationBand a (occupationBandRadius n) (m (occupationBandRadius n)) p)

theorem hasContinuousOccupationLocalTime_measurableSet (a : ℝ) (m : ℝ → ℝ) :
    MeasurableSet {p | HasContinuousOccupationLocalTime a m p} :=
  StronglyMeasurable.measurableSet_exists_tendsto (fun n =>
    (continuousPathOccupationBand_measurable a (occupationBandRadius n)
      (m (occupationBandRadius n))).stronglyMeasurable)

theorem continuousPathLocalTime_measurable (a : ℝ) (m : ℝ → ℝ) :
    Measurable (continuousPathLocalTime a m) :=
  (StronglyMeasurable.limUnder (fun n =>
    (continuousPathOccupationBand_measurable a (occupationBandRadius n)
      (m (occupationBandRadius n))).stronglyMeasurable)).measurable

theorem continuousPathLocalTime_eq_of_tendsto (a : ℝ) (m : ℝ → ℝ)
    (p l : ReversibleNeumannFullPath)
    (h : Tendsto (fun n => continuousPathOccupationBand a (occupationBandRadius n)
      (m (occupationBandRadius n)) p) atTop (𝓝 l)) : continuousPathLocalTime a m p = l :=
  h.limUnder_eq

theorem HasContinuousOccupationLocalTime.tendsto {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p) :
    Tendsto (fun n => continuousPathOccupationBand a (occupationBandRadius n)
      (m (occupationBandRadius n)) p) atTop (𝓝 (continuousPathLocalTime a m p)) := by
  obtain ⟨l, hl⟩ := h
  rw [continuousPathLocalTime_eq_of_tendsto a m p l hl]
  exact hl

theorem HasContinuousOccupationLocalTime.eval_tendsto {a : ℝ} {m : ℝ → ℝ}
    {p : ReversibleNeumannFullPath} (h : HasContinuousOccupationLocalTime a m p) (t : ℝ≥0) :
    Tendsto (fun n => continuousPathOccupationBand a (occupationBandRadius n)
      (m (occupationBandRadius n)) p t) atTop (𝓝 (continuousPathLocalTime a m p t)) :=
  (continuous_eval_const t).continuousAt.tendsto.comp h.tendsto

end TimeTraps.Probability

end
