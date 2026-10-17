module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemHistoryData

@[expose] public section

/-! Every finite-dimensional law of the original Neumann martingale
problem is unique. Induction on the largest member of an arbitrary finite
time set uses only the derived extension of a common past law. Repeated or
unordered indexed observations are recovered by measurable projection. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {A : IntervalMedium} {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
variable {G : Filtration ℝ≥0 mΩ} {F : Filtration ℝ≥0 mΩ'}
variable {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.finite_history_law_eq
    (hX : ReversibleNeumannMartingaleProblem A X G μ x)
    (hY : ReversibleNeumannMartingaleProblem A Y F ν x) (S : Finset ℝ≥0) :
    μ.map (finiteTimeHistory S X) = ν.map (finiteTimeHistory S Y) := by
  induction S using Finset.induction_on_max with
  | empty =>
      have heX : finiteTimeHistory ∅ X = (fun _ => fun _ => (0 : ℝ)) := by
        funext ω t
        simp only [finiteTimeHistory, Finset.notMem_empty, if_false]
      have heY : finiteTimeHistory ∅ Y = (fun _ => fun _ => (0 : ℝ)) := by
        funext ω t
        simp only [finiteTimeHistory, Finset.notMem_empty, if_false]
      rw [heX, heY, Measure.map_const, Measure.map_const]
      simp only [measure_univ, one_smul]
  | insert a S hmax ih =>
      rcases S.eq_empty_or_nonempty with rfl | hS
      · have hm := congrArg (Measure.map (fun z : ℝ => finiteTimeHistoryUpdate a ((fun _ => 0), z)))
          (hX.one_time_law_eq hY a)
        rw [Measure.map_map (finiteTimeHistory_singleton_measurable a)
          ((hX.adapted a).mono (G.le a)).measurable,
          Measure.map_map (finiteTimeHistory_singleton_measurable a)
          ((hY.adapted a).mono (F.le a)).measurable] at hm
        have heX : (fun z : ℝ => finiteTimeHistoryUpdate a ((fun _ => 0), z)) ∘ X a =
            finiteTimeHistory {a} X := by
          funext ω t
          simp only [Function.comp_def, finiteTimeHistory, finiteTimeHistoryUpdate, Finset.mem_singleton]
          split_ifs with ht
          · simp only [ht]
          · rfl
        have heY : (fun z : ℝ => finiteTimeHistoryUpdate a ((fun _ => 0), z)) ∘ Y a =
            finiteTimeHistory {a} Y := by
          funext ω t
          simp only [Function.comp_def, finiteTimeHistory, finiteTimeHistoryUpdate, Finset.mem_singleton]
          split_ifs with ht
          · simp only [ht]
          · rfl
        exact (congrArg (fun Z => μ.map Z) heX).symm.trans (hm.trans (congrArg (fun Z => ν.map Z) heY))
      · let b := S.max' hS
        have hb : b ∈ S := Finset.max'_mem S hS
        have hSb : ∀ r ∈ S, r ≤ b := fun r hr => Finset.le_max' S r hr
        have hba : b ≤ a := (hmax b hb).le
        have hj := hX.extend_past_law hY b (a - b)
          (hX.history_adapted S b hSb) (hY.history_adapted S b hSb)
          (measurable_pi_apply b)
          (fun ω => show finiteTimeHistory S X ω b = X b ω by simp only [finiteTimeHistory, if_pos hb])
          (fun ω => show finiteTimeHistory S Y ω b = Y b ω by simp only [finiteTimeHistory, if_pos hb]) ih
        rw [add_tsub_cancel_of_le hba] at hj
        have hm := congrArg (Measure.map (finiteTimeHistoryUpdate a)) hj
        rw [Measure.map_map (finiteTimeHistoryUpdate_measurable a)
          ((hX.history_measurable S).prodMk ((hX.adapted a).mono (G.le a)).measurable),
          Measure.map_map (finiteTimeHistoryUpdate_measurable a)
          ((hY.history_measurable S).prodMk ((hY.adapted a).mono (F.le a)).measurable)] at hm
        have heX : finiteTimeHistoryUpdate a ∘ (fun ω => (finiteTimeHistory S X ω, X a ω)) =
            finiteTimeHistory (insert a S) X := funext (fun ω => (finiteTimeHistory_insert S a X ω).symm)
        have heY : finiteTimeHistoryUpdate a ∘ (fun ω => (finiteTimeHistory S Y ω, Y a ω)) =
            finiteTimeHistory (insert a S) Y := funext (fun ω => (finiteTimeHistory_insert S a Y ω).symm)
        exact (congrArg (fun Z => μ.map Z) heX).symm.trans (hm.trans (congrArg (fun Z => ν.map Z) heY))

theorem ReversibleNeumannMartingaleProblem.finite_time_law_eq
    (hX : ReversibleNeumannMartingaleProblem A X G μ x)
    (hY : ReversibleNeumannMartingaleProblem A Y F ν x) (S : Finset ℝ≥0) :
    μ.map (fun ω => S.restrict (fun t => X t ω)) = ν.map (fun ω => S.restrict (fun t => Y t ω)) := by
  have hm := congrArg (Measure.map S.restrict) (hX.finite_history_law_eq hY S)
  rw [Measure.map_map (Finset.measurable_restrict S) (hX.history_measurable S),
    Measure.map_map (Finset.measurable_restrict S) (hY.history_measurable S)] at hm
  have heX : S.restrict ∘ finiteTimeHistory S X = (fun ω => S.restrict (fun t => X t ω)) := by
    funext ω t
    exact if_pos t.property
  have heY : S.restrict ∘ finiteTimeHistory S Y = (fun ω => S.restrict (fun t => Y t ω)) := by
    funext ω t
    exact if_pos t.property
  exact (congrArg (fun Z => μ.map Z) heX).symm.trans (hm.trans (congrArg (fun Z => ν.map Z) heY))

end TimeTraps.Probability

end
