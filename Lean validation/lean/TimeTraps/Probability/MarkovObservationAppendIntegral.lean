module

public import TimeTraps.Probability.MarkovObservationAppendState
public import TimeTraps.Probability.MarkovObservationLastState
public import TimeTraps.Probability.MarkovFiniteKernelAppend

@[expose] public section

/-! The finite-kernel append identity transported to the actual sorted
observation tuples, with the transition started at the latest old time. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {α : Type*} [MeasurableSpace α]

set_option backward.isDefEq.respectTransparency false in
theorem finiteMarkovKernel_lintegral_append_transport (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (d e : List ℝ≥0) (t : ℝ≥0)
    (he : e = d ++ [t]) (x : α) {F : (Fin e.length → α) → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F q ∂finiteMarkovKernel K e x) =
      ∫⁻ q, ∫⁻ y, F (fun i => (Fin.snoc q y : Fin (d.length + 1) → α)
        (Fin.cast (by simp [he] : e.length = d.length + 1) i))
        ∂K t (finiteStateLast x q) ∂finiteMarkovKernel K d x := by
  subst e
  exact finiteMarkovKernel_lintegral_append_singleton K d t x hF

theorem observationDurations_insert_max (I : Finset ℝ≥0) {s t : ℝ≥0}
    (hs : s ∈ I) (hmax : ∀ u ∈ I, u ≤ s) (hst : s < t) :
    observationDurations 0 ((insert t I).sort (· ≤ ·)) =
      observationDurations 0 (I.sort (· ≤ ·)) ++ [t - s] := by
  rw [observation_sort_insert_last I (fun u hu => (hmax u hu).trans_lt hst),
    observationDurations_append_singleton, observationLastTime_sorted_max I hs hmax]

set_option backward.isDefEq.respectTransparency false in
theorem observation_lintegral_append (K : ℝ≥0 → Kernel α α)
    [∀ t, IsMarkovKernel (K t)] (x : α) (I : Finset ℝ≥0) {s t : ℝ≥0}
    (hs : s ∈ I) (hmax : ∀ u ∈ I, u ≤ s) (hst : s < t)
    {F : (Fin (observationDurations 0 ((insert t I).sort (· ≤ ·))).length → α) → ℝ≥0∞}
    (hF : Measurable F) :
    (∫⁻ q, F q ∂finiteMarkovKernel K (observationDurations 0 ((insert t I).sort (· ≤ ·))) x) =
      ∫⁻ q, ∫⁻ y, F (observationTupleSnoc I t (fun u hu => (hmax u hu).trans_lt hst) q y)
        ∂K (t - s) (observationState I q ⟨s, hs⟩)
        ∂finiteMarkovKernel K (observationDurations 0 (I.sort (· ≤ ·))) x := by
  refine (finiteMarkovKernel_lintegral_append_transport K _ _ (t - s)
    (observationDurations_insert_max I hs hmax hst) x hF).trans ?_
  apply lintegral_congr
  intro q
  rw [finiteStateLast_observationState x I hs hmax q]
  apply lintegral_congr
  intro y
  apply congrArg F
  funext i
  apply congrArg (Fin.snoc q y : Fin ((observationDurations 0 (I.sort (· ≤ ·))).length + 1) → α)
  apply Fin.ext
  rfl

end TimeTraps.Probability
