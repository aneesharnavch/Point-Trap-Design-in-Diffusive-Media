module

public import TimeTraps.Probability.MarkovObservationAppendLaw

@[expose] public section

/-! The canonical finite-dimensional laws imply the joint law of any
finite past containing its latest time and one later process value. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

theorem process_finite_past_future_law (μ : Measure Ω) (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (X : ℝ≥0 → Ω → α)
    (hX : ∀ t, Measurable (X t))
    (hLaw : ∀ I : Finset ℝ≥0, μ.map (fun ω (r : I) => X r.val ω) = markovObservationFamily K x I)
    (I : Finset ℝ≥0) {s t : ℝ≥0} (hs : s ∈ I) (hmax : ∀ u ∈ I, u ≤ s) (hst : s < t) :
    μ.map (fun ω => ((fun r : I => X r.val ω), X t ω)) =
      (μ.map (fun ω (r : I) => X r.val ω)) ⊗ₘ
        (K (t - s)).comap (fun q => q ⟨s, hs⟩) (measurable_pi_apply _) := by
  have hm : Measurable (fun ω (r : ↥(insert t I)) => X r.val ω) :=
    measurable_pi_lambda _ (fun r => hX r.val)
  calc
    _ = (μ.map (fun ω (r : ↥(insert t I)) => X r.val ω)).map (observationExtract I t) :=
      (Measure.map_map (observationExtract_measurable I t) hm).symm
    _ = (markovObservationFamily K x (insert t I)).map (observationExtract I t) := by rw [hLaw]
    _ = (markovObservationFamily K x I) ⊗ₘ
        (K (t - s)).comap (fun q => q ⟨s, hs⟩) (measurable_pi_apply _) :=
      markovObservationFamily_append_law K x I hs hmax hst
    _ = _ := by rw [hLaw]

end TimeTraps.Probability
