module

public import TimeTraps.Probability.BrownianLocalTimeContinuousVersion

@[expose] public section

/-! Finite-horizon Tanaka paths agree on their common interval almost
surely. Countable dense-time identities and continuity give simultaneous
agreement, and all integer-horizon regularity events are retained in one
measurable full-measure event for gluing. The level is fixed throughout. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set TopologicalSpace
open scoped NNReal ENNReal

theorem brownianLocalTimePath_measurable (a : ℝ) (T t : ℝ≥0) :
    Measurable (brownianLocalTimePath a T t) :=
  (brownianLocalTimePath_jointlyMeasurable a T).of_uncurry_left

def brownianLocalTimeCommonTime (S T : ℝ≥0) (k : ℕ) : ℝ≥0 :=
  (denseSeq (BrownianCompactTime (min S T)) k).val

theorem brownianLocalTimePath_eq_of_dense (a : ℝ) (S T : ℝ≥0) (ω : ℕ → ℝ)
    (hω : ∀ k, brownianLocalTimePath a S (brownianLocalTimeCommonTime S T k) ω =
      brownianLocalTimePath a T (brownianLocalTimeCommonTime S T k) ω)
    (t : ℝ≥0) (ht : t ≤ min S T) :
    brownianLocalTimePath a S t ω = brownianLocalTimePath a T t ω := by
  have he : (fun s : BrownianCompactTime (min S T) => brownianLocalTimePath a S s.val ω) =
      (fun s : BrownianCompactTime (min S T) => brownianLocalTimePath a T s.val ω) := by
    apply (denseRange_denseSeq (BrownianCompactTime (min S T))).equalizer
      ((brownianLocalTimePath_continuous a S ω).comp continuous_subtype_val)
      ((brownianLocalTimePath_continuous a T ω).comp continuous_subtype_val)
    exact funext hω
  exact congrFun he ⟨t, zero_le, ht⟩

theorem brownianLocalTimePath_horizon_ae (a : ℝ) (S T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ min S T,
      brownianLocalTimePath a S t ω = brownianLocalTimePath a T t ω := by
  have hd : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ k,
      brownianLocalTimePath a S (brownianLocalTimeCommonTime S T k) ω =
        brownianLocalTimePath a T (brownianLocalTimeCommonTime S T k) ω := by
    apply ae_all_iff.mpr
    intro k
    have ht := (denseSeq (BrownianCompactTime (min S T)) k).property.2
    exact (brownianLocalTimePath_compensation_ae a (ht.trans (min_le_left S T))).trans
      (brownianLocalTimePath_compensation_ae a (ht.trans (min_le_right S T))).symm
  exact hd.mono (fun ω hω t ht => brownianLocalTimePath_eq_of_dense a S T ω hω t ht)

def brownianLocalTimeGlobalRegular (a : ℝ) (ω : ℕ → ℝ) : Prop :=
  (∀ n : ℕ, brownianLocalTimeRegular a n ω) ∧
    ∀ n m k : ℕ,
      brownianLocalTimePath a n (brownianLocalTimeCommonTime n m k) ω =
        brownianLocalTimePath a m (brownianLocalTimeCommonTime n m k) ω

theorem brownianLocalTimeGlobalRegular_measurableSet (a : ℝ) :
    MeasurableSet {ω | brownianLocalTimeGlobalRegular a ω} := by
  have hr : MeasurableSet {ω | ∀ n : ℕ, brownianLocalTimeRegular a n ω} := by
    rw [ofPred_forall]
    exact MeasurableSet.iInter (fun n => brownianLocalTimeRegular_measurableSet a n)
  have he : MeasurableSet {ω | ∀ n m k : ℕ,
      brownianLocalTimePath a n (brownianLocalTimeCommonTime n m k) ω =
        brownianLocalTimePath a m (brownianLocalTimeCommonTime n m k) ω} := by
    simp only [ofPred_forall]
    exact MeasurableSet.iInter (fun n => MeasurableSet.iInter (fun m => MeasurableSet.iInter
      (fun k => measurableSet_eq_fun (brownianLocalTimePath_measurable a n _)
        (brownianLocalTimePath_measurable a m _))))
  exact hr.inter he

theorem brownianLocalTimeGlobalRegular_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, brownianLocalTimeGlobalRegular a ω := by
  have hr : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ, brownianLocalTimeRegular a n ω :=
    ae_all_iff.mpr (fun n => brownianLocalTimeRegular_ae a n)
  have he : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n m k : ℕ,
      brownianLocalTimePath a n (brownianLocalTimeCommonTime n m k) ω =
        brownianLocalTimePath a m (brownianLocalTimeCommonTime n m k) ω := by
    apply ae_all_iff.mpr
    intro n
    apply ae_all_iff.mpr
    intro m
    apply ae_all_iff.mpr
    intro k
    exact (brownianLocalTimePath_horizon_ae a n m).mono (fun _ hω =>
      hω (brownianLocalTimeCommonTime n m k)
        (denseSeq (BrownianCompactTime (min (n : ℝ≥0) (m : ℝ≥0))) k).property.2)
  filter_upwards [hr, he] with ω hreg heq
  exact ⟨hreg, heq⟩

theorem brownianLocalTimeGlobalRegular_eq {a : ℝ} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeGlobalRegular a ω) (n m : ℕ) (t : ℝ≥0)
    (hn : t ≤ n) (hm : t ≤ m) :
    brownianLocalTimePath a n t ω = brownianLocalTimePath a m t ω :=
  brownianLocalTimePath_eq_of_dense a n m ω (hω.2 n m) t (le_min hn hm)

end TimeTraps.Probability

end
