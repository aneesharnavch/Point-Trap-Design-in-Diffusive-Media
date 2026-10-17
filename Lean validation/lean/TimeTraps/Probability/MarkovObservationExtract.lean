module

public import TimeTraps.Probability.MarkovObservationAppendState
public import Mathlib.Probability.Kernel.Composition.MeasureCompProd

@[expose] public section

/-! Measurable extraction of a finite past and one newly observed state
from the canonical finite-time tuple. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

noncomputable def observationExtract (I : Finset ℝ≥0) (t : ℝ≥0)
    (q : ↥(insert t I) → α) : (I → α) × α :=
  (fun r => q ⟨r.val, Finset.mem_insert_of_mem r.property⟩,
    q ⟨t, Finset.mem_insert_self t I⟩)

theorem observationExtract_measurable (I : Finset ℝ≥0) (t : ℝ≥0) :
    Measurable (observationExtract (α := α) I t) :=
  (measurable_pi_lambda _ (fun _ => measurable_pi_apply _)).prodMk (measurable_pi_apply _)

omit [MeasurableSpace α] in
theorem observationExtract_snoc (I : Finset ℝ≥0) (t : ℝ≥0)
    (ht : ∀ u ∈ I, u < t)
    (q : Fin (observationDurations 0 (I.sort (· ≤ ·))).length → α) (y : α) :
    observationExtract I t (observationState (insert t I) (observationTupleSnoc I t ht q y)) =
      (observationState I q, y) := by
  apply Prod.ext
  · funext r
    exact observationTupleSnoc_old I t ht q y r
  · exact observationTupleSnoc_new I t ht q y

theorem markovObservationFamily_lintegral (K : ℝ≥0 → Kernel α α)
    (x : α) (I : Finset ℝ≥0) {F : (I → α) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂markovObservationFamily K x I) =
      ∫⁻ q, F (observationState I q)
        ∂finiteMarkovKernel K (observationDurations 0 (I.sort (· ≤ ·))) x :=
  Kernel.lintegral_map _ (observationState_measurable I) x hF

end TimeTraps.Probability
