module

public import TimeTraps.Probability.BrownianLocalTimeSupportEvent
public import Mathlib.Data.NNRat.Encodable

@[expose] public section

/-! At each fixed level there is one measurable event of full measure
on which every rational-endpoint interval staying uniformly away from
that level has constant global Tanaka path. The countable event uses
reciprocal integer distances; the resulting flatness allows any positive
distance and every real time between the two rational endpoints. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

def brownianLocalTimeSupportRegular (a : ℝ) (ω : ℕ → ℝ) : Prop :=
  BrownianDyadicRegular ω ∧ ∀ (S T : ℚ≥0) (hST : (S : ℝ≥0) ≤ (T : ℝ≥0)) (n : ℕ),
    brownianLocalTimeAwayEvent a (1 / ((n : ℝ) + 1)) S T hST ω →
      brownianLocalTimeGlobalPath a T ω = brownianLocalTimeGlobalPath a S ω

theorem brownianLocalTimeSupportRegular_measurableSet (a : ℝ) :
    MeasurableSet {ω | brownianLocalTimeSupportRegular a ω} := by
  apply brownianDyadicRegular_measurableSet.inter
  change MeasurableSet {ω | ∀ (S T : ℚ≥0) (hST : (S : ℝ≥0) ≤ (T : ℝ≥0)) (n : ℕ),
    brownianLocalTimeAwayEvent a (1 / ((n : ℝ) + 1)) S T hST ω →
      brownianLocalTimeGlobalPath a T ω = brownianLocalTimeGlobalPath a S ω}
  simp only [ofPred_forall]
  exact MeasurableSet.iInter (fun S => MeasurableSet.iInter (fun T =>
    MeasurableSet.iInter (fun hST => MeasurableSet.iInter (fun n =>
      (brownianLocalTimeAwayEvent_measurableSet a (1 / ((n : ℝ) + 1)) S T hST).imp
        (measurableSet_eq_fun (brownianLocalTimeGlobalPath_measurable a T)
          (brownianLocalTimeGlobalPath_measurable a S))))))

theorem brownianLocalTimeSupportRegular_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianLocalTimeSupportRegular a ω := by
  have he : ∀ᵐ ω ∂brownianDyadicMeasure,
      ∀ (S T : ℚ≥0) (hST : (S : ℝ≥0) ≤ (T : ℝ≥0)) (n : ℕ),
        brownianLocalTimeAwayEvent a (1 / ((n : ℝ) + 1)) S T hST ω →
          brownianLocalTimeGlobalPath a T ω = brownianLocalTimeGlobalPath a S ω := by
    apply ae_all_iff.mpr
    intro S
    apply ae_all_iff.mpr
    intro T
    apply ae_all_iff.mpr
    intro hST
    apply ae_all_iff.mpr
    intro n
    exact brownianLocalTimeGlobalPath_eq_on_away_event a (by positivity) hST
  filter_upwards [brownianDyadic_regular_ae, he] with ω hreg hflat
  exact ⟨hreg, hflat⟩

theorem brownianLocalTimeSupportRegular_flat {a : ℝ} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeSupportRegular a ω) (S T : ℚ≥0)
    (hST : (S : ℝ≥0) ≤ (T : ℝ≥0)) {δ : ℝ} (hδ : 0 < δ)
    (haway : ∀ s ∈ Icc (S : ℝ≥0) (T : ℝ≥0), δ ≤ |brownianDyadicPath s ω - a|) :
    ∀ s ∈ Icc (S : ℝ≥0) (T : ℝ≥0),
      brownianLocalTimeGlobalPath a s ω = brownianLocalTimeGlobalPath a S ω := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hδ
  have he : brownianLocalTimeGlobalPath a T ω = brownianLocalTimeGlobalPath a S ω := by
    apply hω.2 S T hST n
    refine ⟨hω.1, fun k => ?_⟩
    exact hn.le.trans (haway _ (brownianLocalTimeAwayProbe S T hST k).property)
  intro s hs
  apply le_antisymm
  · have hh := brownianLocalTimeGlobalPath_monotone a ω hs.2
    exact hh.trans_eq he
  · exact brownianLocalTimeGlobalPath_monotone a ω hs.1

end TimeTraps.Probability
