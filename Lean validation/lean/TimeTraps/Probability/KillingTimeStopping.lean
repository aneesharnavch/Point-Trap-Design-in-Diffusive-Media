module

public import TimeTraps.Probability.KillingTime

@[expose] public section

/-! The strict first-exceedance time is a stopping time in a right-continuous
filtration. Rational times describe `{τ < t}` exactly for a nondecreasing
clock. Right continuity then supplies `{τ ≤ t}` without changing the strict
threshold convention or excluding flat intervals. Path continuity is not
needed for this result. -/

namespace TimeTraps.Probability

open Set MeasureTheory

theorem strictKillingTime_lt_iff_rational (A : ℝ → ℝ) (E t : ℝ)
    (hm : MonotoneOn A (Ici (0 : ℝ))) :
    strictKillingTime A E < (t : WithTop ℝ) ↔
      ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧ E < A (q : ℝ) := by
  constructor
  · intro h
    obtain ⟨s, hs, hAs⟩ := hittingAfter_lt_iff.mp h
    obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn hs.2
    refine ⟨q, hs.1.trans hsq.le, hqt, ?_⟩
    exact hAs.trans_le (hm hs.1 (hs.1.trans hsq.le) hsq.le)
  · rintro ⟨q, hq, hqt, hAq⟩
    exact hittingAfter_lt_iff.mpr ⟨(q : ℝ), ⟨hq, hqt⟩, hAq⟩

theorem strictKillingTime_lt_measurable {Ω : Type*} [m : MeasurableSpace Ω]
    (F : Filtration ℝ m) (A : ℝ → Ω → ℝ) (E : Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable[F t] (A t))
    (hE : Measurable[F 0] E)
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) (t : ℝ) :
    MeasurableSet[F t] {ω | strictKillingTime (fun s => A s ω) (E ω) < (t : WithTop ℝ)} := by
  have hs : {ω | strictKillingTime (fun s => A s ω) (E ω) < (t : WithTop ℝ)} =
      ⋃ q : ℚ, ⋃ (_ : 0 ≤ (q : ℝ)), ⋃ (_ : (q : ℝ) < t),
        {ω | E ω < A (q : ℝ) ω} := by
    ext ω
    simp only [mem_iUnion, mem_ofPred_eq, exists_prop]
    exact strictKillingTime_lt_iff_rational (fun s => A s ω) (E ω) t (hm ω)
  rw [hs]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun hq =>
    MeasurableSet.iUnion fun hqt => ?_
  exact measurableSet_lt (hE.mono (F.mono (hq.trans hqt.le)) le_rfl)
    ((hA (q : ℝ) hq).mono (F.mono hqt.le) le_rfl)

theorem strictKillingTime_isStoppingTime {Ω : Type*} [m : MeasurableSpace Ω]
    (F : Filtration ℝ m) [F.IsRightContinuous] (A : ℝ → Ω → ℝ) (E : Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable[F t] (A t))
    (hE : Measurable[F 0] E)
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    IsStoppingTime F (fun ω => strictKillingTime (fun s => A s ω) (E ω)) := by
  exact isStoppingTime_of_measurableSet_lt_of_isRightContinuous
    (strictKillingTime_lt_measurable F A E hA hE hm)

theorem strictKillingTime_isStoppingTime_rightCont {Ω : Type*} [m : MeasurableSpace Ω]
    (F : Filtration ℝ m) (A : ℝ → Ω → ℝ) (E : Ω → ℝ)
    (hA : ∀ t : ℝ, 0 ≤ t → Measurable[F t] (A t))
    (hE : Measurable[F 0] E)
    (hm : ∀ ω, MonotoneOn (fun s => A s ω) (Ici (0 : ℝ))) :
    IsStoppingTime F.rightCont (fun ω => strictKillingTime (fun s => A s ω) (E ω)) := by
  exact strictKillingTime_isStoppingTime F.rightCont A E
    (fun t ht => (hA t ht).mono (F.le_rightCont t) le_rfl)
    (hE.mono (F.le_rightCont 0) le_rfl) hm

end TimeTraps.Probability
