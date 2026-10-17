module

public import TimeTraps.Probability.BrownianIntegralTruncationAmbient
public import TimeTraps.Probability.BrownianIntegralRefinement

@[expose] public section

/-! The actual time cutoff truncates the right endpoint of each elementary
process. Intervals starting after the cutoff vanish. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

theorem brownianElementaryProcess_cutoff (s u t : ℝ≥0) (ξ : Ω → ℝ) (p : ℝ × Ω) :
    (brownianTimePast t).indicator (brownianElementaryProcess s u ξ) p =
      brownianElementaryProcess s (min u t) ξ p := by
  unfold brownianTimePast brownianElementaryProcess brownianIntervalIndicator
  simp only [Set.indicator_apply, mem_ofPred_eq, mem_Ioc]
  change (if p.1 ≤ t.val then (if s.val < p.1 ∧ p.1 ≤ u.val then 1 else 0) * ξ p.2 else 0) =
    (if s.val < p.1 ∧ p.1 ≤ min u.val t.val then 1 else 0) * ξ p.2
  by_cases ht : p.1 ≤ t.val
  · simp only [ht, ite_true, le_min_iff, and_true]
  · have hn : ¬ (s.val < p.1 ∧ p.1 ≤ min u.val t.val) := by
      intro h
      exact ht (h.2.trans (min_le_right _ _))
    simp only [ht, ite_false, hn, zero_mul]

theorem brownianElementaryProcess_zero_of_end_le {s t : ℝ≥0} (hts : t ≤ s) (ξ : Ω → ℝ) :
    brownianElementaryProcess s t ξ = 0 := by
  funext p
  have h : Ioc s.val t.val = ∅ := Ioc_eq_empty_of_le hts
  simp only [brownianElementaryProcess, brownianIntervalIndicator, h, indicator_empty, zero_mul,
    Pi.zero_apply]

theorem brownianTimeCutoffAmbient_elementary_coe (a : BrownianIntegralElementary B hBm P)
    (t : ℝ≥0) :
    brownianTimeCutoffAmbient P t a.processL2 =ᵐ[volume.prod P]
      brownianElementaryProcess a.left (min a.right t) a.coefficient := by
  filter_upwards [brownianTimeCutoffAmbient_coe P t a.processL2, a.processL2_coe] with p hc ha
  rw [hc, ← brownianElementaryProcess_cutoff]
  by_cases hp : p ∈ brownianTimePast t
  · simp only [indicator_of_mem hp]
    exact ha
  · simp only [indicator_of_notMem hp]

theorem brownianTimeCutoffAmbient_elementary_zero (a : BrownianIntegralElementary B hBm P)
    {t : ℝ≥0} (ht : t ≤ a.left) : brownianTimeCutoffAmbient P t a.processL2 = 0 := by
  apply Lp.ext
  have h := brownianTimeCutoffAmbient_elementary_coe a t
  rw [brownianElementaryProcess_zero_of_end_le ((min_le_right a.right t).trans ht)] at h
  exact h.trans (Lp.coeFn_zero ℝ 2 (volume.prod P)).symm

theorem brownianTimeCutoffAmbient_elementary (a : BrownianIntegralElementary B hBm P)
    {t : ℝ≥0} (ht : a.left ≤ t) :
    brownianTimeCutoffAmbient P t a.processL2 =
      (a.refineLeft (min a.right t) (le_min a.ordered ht)).processL2 := by
  apply Lp.ext
  exact (brownianTimeCutoffAmbient_elementary_coe a t).trans
    (a.refineLeft (min a.right t) (le_min a.ordered ht)).processL2_coe.symm

theorem brownianTimeCutoffAmbient_elementary_full (a : BrownianIntegralElementary B hBm P)
    {t : ℝ≥0} (ht : a.right ≤ t) : brownianTimeCutoffAmbient P t a.processL2 = a.processL2 := by
  apply Lp.ext
  have h := brownianTimeCutoffAmbient_elementary_coe a t
  rw [min_eq_left ht] at h
  exact h.trans a.processL2_coe.symm

end TimeTraps.Probability
