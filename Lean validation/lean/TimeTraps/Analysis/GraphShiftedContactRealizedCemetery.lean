module

public import TimeTraps.Analysis.GraphShiftedContactRealizedHeatSemigroup
public import TimeTraps.Probability.CemeteryKernelComposition

@[expose] public section

/-! The actual killed graph transition, with its lost probability sent
to one absorbing cemetery state. This is a Markov kernel semigroup;
construction of a path process is a separate obligation. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory TimeTraps.Analysis TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def GraphShiftedContactOperatorProblem.realizedKilledTransition (P : GraphShiftedContactOperatorProblem V E)
    (t : ℝ≥0) : Kernel (GraphRealization P.geometry ⊕ Unit) (GraphRealization P.geometry ⊕ Unit) :=
  cemeteryKernel (P.realizedTransition t)

instance GraphShiftedContactOperatorProblem.realizedKilledTransition_markov (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) :
    IsMarkovKernel (P.realizedKilledTransition t) :=
  cemeteryKernel_isMarkov _ (P.realizedTransition_mass_le_one t)

theorem GraphShiftedContactOperatorProblem.realizedKilledTransition_zero (P : GraphShiftedContactOperatorProblem V E) :
    P.realizedKilledTransition 0 = Kernel.id := by
  unfold realizedKilledTransition
  rw [P.realizedTransition_zero, cemeteryKernel_id]

theorem GraphShiftedContactOperatorProblem.realizedKilledTransition_add (P : GraphShiftedContactOperatorProblem V E) (s t : ℝ≥0) :
    P.realizedKilledTransition (s + t) =
      P.realizedKilledTransition t ∘ₖ P.realizedKilledTransition s := by
  unfold realizedKilledTransition
  rw [cemeteryKernel_comp _ _ (P.realizedTransition_mass_le_one s)
    (P.realizedTransition_mass_le_one t), ← P.realizedTransition_add]

theorem GraphShiftedContactOperatorProblem.realizedKilledTransition_dead (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) :
    P.realizedKilledTransition t (Sum.inr ()) = Measure.dirac (Sum.inr ()) :=
  cemeteryKernel_dead _

theorem GraphShiftedContactOperatorProblem.realizedKilledTransition_live (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0)
    (x : GraphRealization P.geometry) {A : Set (GraphRealization P.geometry)} (hA : MeasurableSet A) :
    P.realizedKilledTransition t (Sum.inl x) (Sum.inl '' A) = P.realizedTransition t x A :=
  cemeteryKernel_live_set _ x hA

theorem GraphShiftedContactOperatorProblem.realizedKilledTransition_dead_mass (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0)
    (x : GraphRealization P.geometry) :
    P.realizedKilledTransition t (Sum.inl x) {Sum.inr ()} = 1 - P.realizedTransition t x univ := by
  rw [cemeteryProbability_dead_mass]
  have hl := P.realizedKilledTransition_live t x MeasurableSet.univ
  simpa only [image_univ] using congrArg (fun r : ℝ≥0∞ => 1 - r) hl

end TimeTraps.Analysis
