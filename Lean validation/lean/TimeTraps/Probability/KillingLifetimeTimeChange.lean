module

public import TimeTraps.Probability.KillingLifetimeConvention
public import TimeTraps.Analysis.PositiveTimeChangeInverse

@[expose] public section

/-! Literal first attainment under an increasing onto change of
nonnegative time. The extended map preserves infinity. The proof maps
the entire set of threshold hits, so no monotonicity, continuity, or
eventual attainment assumption is imposed on the hazard itself. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped NNReal

noncomputable def positiveClockLifetimeMap (C : ℝ≥0 → ℝ≥0) (τ : WithTop ℝ) : WithTop ℝ :=
  WithTop.map (fun r : ℝ => (C r.toNNReal : ℝ)) τ

theorem positiveClockLifetimeMap_top (C : ℝ≥0 → ℝ≥0) :
    positiveClockLifetimeMap C ⊤ = ⊤ := rfl

theorem positiveClockLifetimeMap_coe (C : ℝ≥0 → ℝ≥0) (r : ℝ) :
    positiveClockLifetimeMap C (r : WithTop ℝ) = ((C r.toNNReal : ℝ) : WithTop ℝ) := rfl

theorem positiveClockLifetimeMap_nonneg (C : ℝ≥0 → ℝ≥0) (τ : WithTop ℝ) :
    (0 : WithTop ℝ) ≤ positiveClockLifetimeMap C τ := by
  cases τ with
  | top => exact le_top
  | coe r => exact WithTop.coe_le_coe.mpr (C r.toNNReal).coe_nonneg

theorem positiveClockLifetimeMap_lt_iff (e : ℝ≥0 ≃o ℝ≥0) {τ : WithTop ℝ}
    (hτ : 0 ≤ τ) {t : ℝ} (ht : 0 ≤ t) :
    positiveClockLifetimeMap e τ < (t : WithTop ℝ) ↔
      τ < ((e.symm t.toNNReal : ℝ) : WithTop ℝ) := by
  cases τ with
  | top => simp only [positiveClockLifetimeMap_top, not_top_lt]
  | coe r =>
    have hr : 0 ≤ r := WithTop.coe_le_coe.mp hτ
    simp only [positiveClockLifetimeMap_coe, WithTop.coe_lt_coe]
    have ho : e r.toNNReal < t.toNNReal ↔ r.toNNReal < e.symm t.toNNReal := by
      conv_lhs => rw [← e.apply_symm_apply t.toNNReal]
      exact e.lt_iff_lt
    have ht' : (t.toNNReal : ℝ) = t := Real.coe_toNNReal t ht
    have hr' : (r.toNNReal : ℝ) = r := Real.coe_toNNReal r hr
    constructor
    · intro h
      have hh : e r.toNNReal < t.toNNReal := by exact_mod_cast (h.trans_eq ht'.symm)
      have hh' : (r.toNNReal : ℝ) < (e.symm t.toNNReal : ℝ) := ho.mp hh
      exact hr' ▸ hh'
    · intro h
      have hh : r.toNNReal < e.symm t.toNNReal := by exact_mod_cast (hr'.trans_lt h)
      have hh' : (e r.toNNReal : ℝ) < (t.toNNReal : ℝ) := ho.mpr hh
      exact hh'.trans_eq ht'

theorem attainmentKillingTime_inverse_lt_iff (e : ℝ≥0 ≃o ℝ≥0) (A : ℝ → ℝ) (E t : ℝ)
    (ht : 0 ≤ t) :
    attainmentKillingTime (fun r => A (e.symm r.toNNReal : ℝ)) E < (t : WithTop ℝ) ↔
      attainmentKillingTime A E < ((e.symm t.toNNReal : ℝ) : WithTop ℝ) := by
  simp only [attainmentKillingTime, hittingAfter_lt_iff, mem_Ici]
  constructor
  · rintro ⟨r, hr, hAr⟩
    have hr' : r.toNNReal < t.toNNReal := by
      change (r.toNNReal : ℝ) < (t.toNNReal : ℝ)
      rw [Real.coe_toNNReal r hr.1, Real.coe_toNNReal t ht]
      exact hr.2
    exact ⟨(e.symm r.toNNReal : ℝ), ⟨(e.symm r.toNNReal).coe_nonneg,
      e.symm.strictMono hr'⟩, hAr⟩
  · rintro ⟨r, hr, hAr⟩
    have hr' : r.toNNReal < e.symm t.toNNReal := by
      change (r.toNNReal : ℝ) < (e.symm t.toNNReal : ℝ)
      rw [Real.coe_toNNReal r hr.1]
      exact hr.2
    have he : (e r.toNNReal : ℝ) < t := by
      have h := e.strictMono hr'
      rw [e.apply_symm_apply] at h
      change (e r.toNNReal : ℝ) < (t.toNNReal : ℝ) at h
      rwa [Real.coe_toNNReal t ht] at h
    refine ⟨(e r.toNNReal : ℝ), ⟨(e r.toNNReal).coe_nonneg, he⟩, ?_⟩
    simpa only [Real.toNNReal_coe, e.symm_apply_apply, Real.coe_toNNReal r hr.1] using hAr

theorem attainmentKillingTime_inverse (e : ℝ≥0 ≃o ℝ≥0) (A : ℝ → ℝ) (E : ℝ) :
    attainmentKillingTime (fun r => A (e.symm r.toNNReal : ℝ)) E =
      positiveClockLifetimeMap e (attainmentKillingTime A E) := by
  have he (t : ℝ) :
      attainmentKillingTime (fun r => A (e.symm r.toNNReal : ℝ)) E < (t : WithTop ℝ) ↔
        positiveClockLifetimeMap e (attainmentKillingTime A E) < (t : WithTop ℝ) := by
    by_cases ht : 0 ≤ t
    · rw [attainmentKillingTime_inverse_lt_iff e A E t ht,
        positiveClockLifetimeMap_lt_iff e (attainmentKillingTime_nonneg A E) ht]
    · have ht' : (t : WithTop ℝ) ≤ 0 := WithTop.coe_le_coe.mpr (le_of_not_ge ht)
      exact iff_of_false
        (not_lt.mpr (ht'.trans (attainmentKillingTime_nonneg _ _)))
        (not_lt.mpr (ht'.trans (positiveClockLifetimeMap_nonneg _ _)))
  apply le_antisymm
  · exact WithTop.le_of_forall_lt_iff_le.mp (fun t ht => ((he t).mpr ht).le)
  · exact WithTop.le_of_forall_lt_iff_le.mp (fun t ht => ((he t).mp ht).le)

theorem positiveClockLifetimeMap_eq_top_iff (C : ℝ≥0 → ℝ≥0) (τ : WithTop ℝ) :
    positiveClockLifetimeMap C τ = ⊤ ↔ τ = ⊤ := by
  cases τ with
  | top => simp only [positiveClockLifetimeMap_top]
  | coe r => simp only [positiveClockLifetimeMap_coe, WithTop.coe_ne_top]

theorem attainmentKillingTime_inverse_eq_top_iff (e : ℝ≥0 ≃o ℝ≥0) (A : ℝ → ℝ) (E : ℝ) :
    attainmentKillingTime (fun r => A (e.symm r.toNNReal : ℝ)) E = ⊤ ↔
      attainmentKillingTime A E = ⊤ := by
  rw [attainmentKillingTime_inverse, positiveClockLifetimeMap_eq_top_iff]

end TimeTraps.Probability
