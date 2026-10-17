module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemLaw
public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemPathData

@[expose] public section

/-! Uniqueness holds for the actual Borel law of continuous paths on
every finite horizon, in addition to the full coordinate-product law.
Dense countable evaluations determine each continuous path and form a
proved measurable embedding of the Polish path space. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval TopologicalSpace
open scoped NNReal ENNReal Topology

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {A : IntervalMedium} {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
variable {G : Filtration ℝ≥0 mΩ} {F : Filtration ℝ≥0 mΩ'}
variable {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.continuous_path_law_eq
    (hX : ReversibleNeumannMartingaleProblem A X G μ x)
    (hY : ReversibleNeumannMartingaleProblem A Y F ν x) (H : ℝ≥0) :
    μ.map (hX.continuousPath H) = ν.map (hY.continuousPath H) := by
  let : Nonempty (Icc (0 : ℝ≥0) H) := ⟨⟨0, le_rfl, bot_le⟩⟩
  apply (reversibleNeumannContinuousPathSample_measurableEmbedding H).map_injective
  rw [Measure.map_map (reversibleNeumannContinuousPathSample_measurableEmbedding H).measurable
      (hX.continuousPath_measurable H),
    Measure.map_map (reversibleNeumannContinuousPathSample_measurableEmbedding H).measurable
      (hY.continuousPath_measurable H)]
  exact hX.indexed_observation_law_eq hY (fun n => (denseSeq (Icc (0 : ℝ≥0) H) n).val)

theorem ReversibleNeumannMartingaleProblem.continuous_path_law_reference
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    (hx : x ∈ Icc A.source.left A.source.right) (H : ℝ≥0) :
    μ.map (h.continuousPath H) = brownianCompletedMeasure.map
      (ReversibleNeumannMartingaleProblem.continuousPath (Ω := BrownianCompletedSample)
        (reversibleResistancePath_martingaleProblem A hx) H) :=
  h.continuous_path_law_eq (Ω' := BrownianCompletedSample)
    (Y := fun t (ω : BrownianCompletedSample) => reversibleResistancePath A x t ω)
    (reversibleResistancePath_martingaleProblem A hx) H

end TimeTraps.Probability

end
