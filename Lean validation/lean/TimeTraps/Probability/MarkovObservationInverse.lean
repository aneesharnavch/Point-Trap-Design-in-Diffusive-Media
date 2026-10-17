module

public import TimeTraps.Probability.MarkovObservationFamily

@[expose] public section

/-! The canonical finite observation reindexing has a literal measurable
inverse. Hence the finite-set law supplies the actual chronological tuple
law without an additional stochastic assumption. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal

variable {α : Type*} [MeasurableSpace α]

noncomputable def observationStateInverse (I : Finset ℝ≥0) (q : I → α) :
    Fin (observationDurations 0 (I.sort (· ≤ ·))).length → α :=
  fun i => q (observationTimeIndex I i)

theorem observationStateInverse_measurable (I : Finset ℝ≥0) :
    Measurable (observationStateInverse (α := α) I) :=
  measurable_pi_lambda _ (fun _ => measurable_pi_apply _)

omit [MeasurableSpace α] in
theorem observationStateInverse_left (I : Finset ℝ≥0)
    (q : Fin (observationDurations 0 (I.sort (· ≤ ·))).length → α) :
    observationStateInverse I (observationState I q) = q := by
  funext i
  exact congrArg q ((observationTimeIndex I).symm_apply_apply i)

omit [MeasurableSpace α] in
theorem observationStateInverse_right (I : Finset ℝ≥0) (q : I → α) :
    observationState I (observationStateInverse I q) = q := by
  funext i
  exact congrArg q ((observationTimeIndex I).apply_symm_apply i)

theorem markovObservationFamily_inverse_map (K : ℝ≥0 → Kernel α α)
    (x : α) (I : Finset ℝ≥0) :
    (markovObservationFamily K x I).map (observationStateInverse I) =
      finiteMarkovKernel K (observationDurations 0 (I.sort (· ≤ ·))) x := by
  change (((finiteMarkovKernel K (observationDurations 0 (I.sort (· ≤ ·)))).map
    (observationState I) x).map (observationStateInverse I)) = _
  rw [Kernel.map_apply _ (observationState_measurable I),
    Measure.map_map (observationStateInverse_measurable I) (observationState_measurable I)]
  have he : observationStateInverse (α := α) I ∘ observationState I = id :=
    funext (observationStateInverse_left I)
  rw [he, Measure.map_id]

theorem process_chronological_law_of_finite_observations {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : ℝ≥0 → Kernel α α) (x : α) (X : ℝ≥0 → Ω → α)
    (hX : ∀ t, Measurable (X t)) (I : Finset ℝ≥0)
    (hI : μ.map (fun ω (t : I) => X t.val ω) = markovObservationFamily K x I) :
    μ.map (fun ω i => X (observationTimeIndex I i).val ω) =
      finiteMarkovKernel K (observationDurations 0 (I.sort (· ≤ ·))) x := by
  have hm : Measurable (fun ω (t : I) => X t.val ω) :=
    measurable_pi_lambda _ (fun t => hX t.val)
  calc
    _ = (μ.map (fun ω (t : I) => X t.val ω)).map (observationStateInverse I) :=
      (Measure.map_map (observationStateInverse_measurable I) hm).symm
    _ = (markovObservationFamily K x I).map (observationStateInverse I) :=
      congrArg (fun ν : Measure (I → α) => ν.map (observationStateInverse I)) hI
    _ = _ := markovObservationFamily_inverse_map K x I

end TimeTraps.Probability
