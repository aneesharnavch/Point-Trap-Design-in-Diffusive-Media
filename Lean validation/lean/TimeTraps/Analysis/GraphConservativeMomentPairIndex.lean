module

public import TimeTraps.Analysis.GraphConservativeMomentPairData

@[expose] public section

/-! Exact coordinates of the two-time observation law after chronological
sorting. The proof uses its actual elapsed times, avoiding a convention
about finite-set enumeration. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable def observationPairIndex {s t : ℝ≥0} (hst : s < t) (i : Fin 2) :
    Fin (observationDurations 0 (({s, t} : Finset ℝ≥0).sort (· ≤ ·))).length :=
  Fin.cast (by rw [observationPair_durations hst]; rfl) i

theorem elapsedObservationTime_cast {d e : List ℝ≥0} (h : d = e) (r : ℝ≥0) (i : Fin d.length) :
    elapsedObservationTime r e (Fin.cast (congrArg List.length h) i) = elapsedObservationTime r d i := by
  subst e
  rfl

theorem observationPairIndex_time_zero {s t : ℝ≥0} (hst : s < t) :
    elapsedObservationTime 0 (observationDurations 0 (({s, t} : Finset ℝ≥0).sort (· ≤ ·)))
      (observationPairIndex hst 0) = s := by
  have he := elapsedObservationTime_cast (observationPair_durations hst).symm 0 (0 : Fin 2)
  exact he.trans (by simp only [elapsedObservationTime, Fin.cons_zero, zero_add])

theorem observationPairIndex_time_one {s t : ℝ≥0} (hst : s < t) :
    elapsedObservationTime 0 (observationDurations 0 (({s, t} : Finset ℝ≥0).sort (· ≤ ·)))
      (observationPairIndex hst 1) = t := by
  have he := elapsedObservationTime_cast (observationPair_durations hst).symm 0 (1 : Fin 2)
  apply he.trans
  simp only [elapsedObservationTime, Fin.cons_one, Fin.cons_zero, zero_add]
  exact add_tsub_cancel_of_le hst.le

variable {α : Type*}

theorem observationState_pair {s t : ℝ≥0} (hst : s < t)
    (q : Fin (observationDurations 0 (({s, t} : Finset ℝ≥0).sort (· ≤ ·))).length → α) :
    (observationState {s, t} q ⟨s, by simp⟩, observationState {s, t} q ⟨t, by simp⟩) =
      (q (observationPairIndex hst 0), q (observationPairIndex hst 1)) := by
  exact Prod.ext
    (observationState_time {s, t} q ⟨s, by simp⟩ _ (observationPairIndex_time_zero hst))
    (observationState_time {s, t} q ⟨t, by simp⟩ _ (observationPairIndex_time_one hst))

theorem finiteMarkovKernel_pair_lintegral_cast [MeasurableSpace α]
    (K : ℝ≥0 → Kernel α α) [∀ t, IsMarkovKernel (K t)] (s u : ℝ≥0) (x : α)
    {d : List ℝ≥0} (hd : d = [s, u])
    {F : α × α → ℝ≥0∞} (hF : Measurable F) :
    (∫⁻ q, F (q (Fin.cast (congrArg List.length hd.symm) (0 : Fin 2)),
      q (Fin.cast (congrArg List.length hd.symm) (1 : Fin 2))) ∂finiteMarkovKernel K d x) =
        ∫⁻ y, ∫⁻ z, F (y, z) ∂K u y ∂K s x := by
  subst d
  exact finiteMarkovKernel_pair_lintegral K s u x hF

end TimeTraps.Probability
