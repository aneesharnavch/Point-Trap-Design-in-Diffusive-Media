module

public import TimeTraps.Probability.KillingTimeStopping

@[expose] public section

/-! The first attainment convention uses the closed threshold set. For a
nondecreasing clock, rational times detect strict upper cuts of both
lifetimes. Excluding the countable collection of rational clock values
therefore identifies the two extended lifetimes, including infinity.
No strict increase, continuity, or eventual attainment is assumed here. -/

namespace TimeTraps.Probability

open Set MeasureTheory

noncomputable def attainmentKillingTime (A : ℝ → ℝ) (E : ℝ) : WithTop ℝ :=
  hittingAfter (fun t (_ : Unit) => A t) (Ici E) 0 ()

theorem attainmentKillingTime_nonneg (A : ℝ → ℝ) (E : ℝ) :
    (0 : WithTop ℝ) ≤ attainmentKillingTime A E :=
  le_hittingAfter ()

theorem attainmentKillingTime_eq_top_iff (A : ℝ → ℝ) (E : ℝ) :
    attainmentKillingTime A E = ⊤ ↔ ∀ t : ℝ, 0 ≤ t → A t < E := by
  simp only [attainmentKillingTime, hittingAfter_eq_top_iff, mem_Ici, not_le]

theorem attainmentKillingTime_lt_iff_rational (A : ℝ → ℝ) (E t : ℝ)
    (hm : MonotoneOn A (Ici (0 : ℝ))) :
    attainmentKillingTime A E < (t : WithTop ℝ) ↔
      ∃ q : ℚ, 0 ≤ (q : ℝ) ∧ (q : ℝ) < t ∧ E ≤ A (q : ℝ) := by
  constructor
  · intro h
    obtain ⟨s, hs, hAs⟩ := hittingAfter_lt_iff.mp h
    obtain ⟨q, hsq, hqt⟩ := exists_rat_btwn hs.2
    refine ⟨q, hs.1.trans hsq.le, hqt, ?_⟩
    exact hAs.trans (hm hs.1 (hs.1.trans hsq.le) hsq.le)
  · rintro ⟨q, hq, hqt, hAq⟩
    exact hittingAfter_lt_iff.mpr ⟨(q : ℝ), ⟨hq, hqt⟩, hAq⟩

theorem strictKillingTime_eq_attainment_of_rational_ne (A : ℝ → ℝ) (E : ℝ)
    (hm : MonotoneOn A (Ici (0 : ℝ)))
    (hne : ∀ q : ℚ, 0 ≤ (q : ℝ) → A (q : ℝ) ≠ E) :
    strictKillingTime A E = attainmentKillingTime A E := by
  have he (t : ℝ) : strictKillingTime A E < (t : WithTop ℝ) ↔
      attainmentKillingTime A E < (t : WithTop ℝ) := by
    rw [strictKillingTime_lt_iff_rational A E t hm,
      attainmentKillingTime_lt_iff_rational A E t hm]
    constructor
    · rintro ⟨q, hq, hqt, hAq⟩
      exact ⟨q, hq, hqt, hAq.le⟩
    · rintro ⟨q, hq, hqt, hAq⟩
      exact ⟨q, hq, hqt, lt_of_le_of_ne hAq (hne q hq).symm⟩
  apply le_antisymm
  · exact WithTop.le_of_forall_lt_iff_le.mp (fun t ht => ((he t).mpr ht).le)
  · exact WithTop.le_of_forall_lt_iff_le.mp (fun t ht => ((he t).mp ht).le)

end TimeTraps.Probability
