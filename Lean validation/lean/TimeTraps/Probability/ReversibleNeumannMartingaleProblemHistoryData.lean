module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemJointLaw
public import Mathlib.Data.Finset.Max
public import Mathlib.Probability.Process.FiniteDimensionalLaws

@[expose] public section

/-! Finite observation histories are represented in the same measurable
function space by setting unobserved coordinates to zero. Inserting a time
is a literal measurable coordinate update; this representation permits
induction on the largest observed time without ordering assumptions. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

def finiteTimeHistory {Ω : Type*} (S : Finset ℝ≥0) (X : ℝ≥0 → Ω → ℝ) (ω : Ω) : ℝ≥0 → ℝ :=
  fun t => if t ∈ S then X t ω else 0

def finiteTimeHistoryUpdate (a : ℝ≥0) (p : (ℝ≥0 → ℝ) × ℝ) : ℝ≥0 → ℝ :=
  fun t => if t = a then p.2 else p.1 t

theorem finiteTimeHistoryUpdate_measurable (a : ℝ≥0) : Measurable (finiteTimeHistoryUpdate a) := by
  apply measurable_pi_lambda
  intro t
  by_cases ht : t = a
  · simpa only [finiteTimeHistoryUpdate, if_pos ht] using measurable_snd
  · simpa only [finiteTimeHistoryUpdate, if_neg ht, Function.comp_def] using (measurable_pi_apply t).comp measurable_fst

theorem finiteTimeHistory_insert {Ω : Type*} (S : Finset ℝ≥0) (a : ℝ≥0)
    (X : ℝ≥0 → Ω → ℝ) (ω : Ω) :
    finiteTimeHistory (insert a S) X ω = finiteTimeHistoryUpdate a (finiteTimeHistory S X ω, X a ω) := by
  funext t
  by_cases ht : t = a
  · subst t
    simp only [finiteTimeHistory, Finset.mem_insert_self, if_true, finiteTimeHistoryUpdate]
  · simp only [finiteTimeHistory, Finset.mem_insert, ht, false_or, finiteTimeHistoryUpdate, if_false]

theorem finiteTimeHistory_singleton_measurable (a : ℝ≥0) :
    Measurable (fun z : ℝ => finiteTimeHistoryUpdate a ((fun _ => 0), z)) :=
  (finiteTimeHistoryUpdate_measurable a).comp (measurable_const.prodMk measurable_id)

theorem ReversibleNeumannMartingaleProblem.history_measurable
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium} {X : ℝ≥0 → Ω → ℝ}
    {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {x : ℝ}
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (S : Finset ℝ≥0) :
    Measurable (finiteTimeHistory S X) := by
  apply measurable_pi_lambda
  intro t
  by_cases ht : t ∈ S
  · simpa only [finiteTimeHistory, if_pos ht] using ((h.adapted t).mono (G.le t)).measurable
  · simpa only [finiteTimeHistory, if_neg ht] using (measurable_const : Measurable (fun _ : Ω => (0 : ℝ)))

theorem ReversibleNeumannMartingaleProblem.history_adapted
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium} {X : ℝ≥0 → Ω → ℝ}
    {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {x : ℝ}
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (S : Finset ℝ≥0) (s : ℝ≥0)
    (hs : ∀ t ∈ S, t ≤ s) : Measurable[G s] (finiteTimeHistory S X) := by
  let : MeasurableSpace Ω := G s
  apply measurable_pi_lambda
  intro t
  by_cases ht : t ∈ S
  · simpa only [finiteTimeHistory, if_pos ht] using ((h.adapted t).mono (G.mono (hs t ht))).measurable
  · simpa only [finiteTimeHistory, if_neg ht] using
      (measurable_const : @Measurable Ω ℝ (G s) _ (fun _ => (0 : ℝ)))

end TimeTraps.Probability

end
