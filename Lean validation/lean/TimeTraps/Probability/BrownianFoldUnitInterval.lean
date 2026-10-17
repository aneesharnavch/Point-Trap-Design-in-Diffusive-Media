module

public import TimeTraps.Probability.BrownianFoldUnitConvergence

@[expose] public section

/-! Clipping each dyadic node from below gives actual unit-coefficient
stochastic sums over a deterministic interval. The coefficients retain
their original sampling times and are adapted at the later clipped nodes.
The corresponding completed integrand is exactly the original step
integrand minus its cutoff at the initial time. Repeated nodes are allowed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianElementaryProcess_after (a b s : ℝ≥0) (ξ : Ω → ℝ) (p : ℝ × Ω) :
    brownianElementaryProcess (max s a) (max s b) ξ p =
      brownianElementaryProcess a b ξ p -
        (brownianTimePast s).indicator (brownianElementaryProcess a b ξ) p := by
  by_cases hs : p.1 ≤ s.val
  · have hn : p.1 ∉ Ioc (max s a).val (max s b).val := by
      intro h
      exact not_lt_of_ge (hs.trans (show s.val ≤ (max s a).val from le_max_left s a)) h.1
    rw [indicator_of_mem (show p ∈ brownianTimePast s from hs), sub_self]
    simp only [brownianElementaryProcess, brownianIntervalIndicator,
      indicator_of_notMem hn, zero_mul]
  · have hlt : s.val < p.1 := lt_of_not_ge hs
    have he : p.1 ∈ Ioc (max s a).val (max s b).val ↔ p.1 ∈ Ioc a.val b.val := by
      constructor
      · intro h
        have hb : p.1 ≤ max s.val b.val := h.2
        exact ⟨(show a.val ≤ (max s a).val from le_max_right s a).trans_lt h.1,
          (le_max_iff.mp hb).resolve_left hs⟩
      · intro h
        exact ⟨max_lt hlt h.1,
          h.2.trans (show b.val ≤ (max s b).val from le_max_right s b)⟩
    rw [indicator_of_notMem (show p ∉ brownianTimePast s from hs), sub_zero]
    unfold brownianElementaryProcess brownianIntervalIndicator
    by_cases hp : p.1 ∈ Ioc a.val b.val
    · rw [indicator_of_mem hp, indicator_of_mem (he.mpr hp)]
    · rw [indicator_of_notMem hp, indicator_of_notMem (mt he.mp hp)]

def brownianFoldUnitIntervalGrid (s t : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n + 1)) : ℝ≥0 :=
  max s (brownianDyadicGrid t n i)

theorem brownianFoldUnitIntervalGrid_monotone (s t : ℝ≥0) (n : ℕ) :
    Monotone (brownianFoldUnitIntervalGrid s t n) := by
  intro i j hij
  exact max_le_max_left s (brownianDyadicGrid_monotone t n hij)

theorem brownianFoldUnitIntervalGrid_zero (s t : ℝ≥0) (n : ℕ) :
    brownianFoldUnitIntervalGrid s t n 0 = s := by
  simp only [brownianFoldUnitIntervalGrid, brownianDyadicGrid_zero, max_eq_left zero_le]

theorem brownianFoldUnitIntervalGrid_last {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) :
    brownianFoldUnitIntervalGrid s t n (Fin.last (2 ^ n)) = t := by
  simp only [brownianFoldUnitIntervalGrid, brownianDyadicGrid_last, max_eq_right hst]

theorem brownianFoldUnitIntervalCoefficient_adapted (hBm : ∀ t, Measurable (B t))
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (s t : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) :
    StronglyMeasurable[brownianNaturalFiltration B hBm
      (brownianFoldUnitIntervalGrid s t n i.castSucc)] (brownianFoldUnitCoefficient B L x σ t n i) :=
  (brownianFoldUnitCoefficient_adapted hBm L hL x σ t n i).mono
    ((brownianNaturalFiltration B hBm).mono (le_max_right _ _))

def brownianFoldUnitIntervalElementary (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (s t : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) : BrownianIntegralElementary B hBm P where
  left := brownianFoldUnitIntervalGrid s t n i.castSucc
  right := brownianFoldUnitIntervalGrid s t n i.succ
  ordered := brownianFoldUnitIntervalGrid_monotone s t n (Fin.castSucc_le_succ i)
  coefficient := brownianFoldUnitCoefficient B L x σ t n i
  adapted := brownianFoldUnitIntervalCoefficient_adapted hBm L hL x σ s t n i
  squareIntegrable := brownianFoldUnitCoefficient_memLp hB hBm L hL x σ t n i

def brownianFoldUnitIntervalIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (s t : ℝ≥0) (n : ℕ) : brownianIntegralSpace B hBm P :=
  brownianElementarySumIntegrand (brownianFoldUnitIntervalElementary hB hBm L hL x σ s t n)

theorem brownianFoldUnitIntervalIntegrand_eq (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (s t : ℝ≥0) (n : ℕ) :
    brownianFoldUnitIntervalIntegrand hB hBm L hL x σ s t n =
      brownianFoldUnitStepIntegrand hB hBm L hL x σ t n -
        brownianTimeCutoff B hBm P s (brownianFoldUnitStepIntegrand hB hBm L hL x σ t n) := by
  let f := brownianFoldUnitStepIntegrand hB hBm L hL x σ t n
  apply Subtype.ext
  change (brownianFoldUnitIntervalIntegrand hB hBm L hL x σ s t n :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =
    (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
      (brownianTimeCutoff B hBm P s f : Lp ℝ 2 ((volume : Measure ℝ).prod P))
  apply Lp.ext
  filter_upwards [brownianElementarySumIntegrand_coe
      (brownianFoldUnitIntervalElementary hB hBm L hL x σ s t n),
    brownianElementarySumIntegrand_coe (brownianFoldUnitElementary hB hBm L hL x σ t n),
    brownianTimeCutoff_coe s f,
    Lp.coeFn_sub (f : Lp ℝ 2 ((volume : Measure ℝ).prod P))
      (brownianTimeCutoff B hBm P s f : Lp ℝ 2 ((volume : Measure ℝ).prod P))]
    with p ha hf hc hd
  rw [hd, Pi.sub_apply, hc]
  change (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p =
    brownianElementarySum (brownianFoldUnitElementary hB hBm L hL x σ t n) p at hf
  change (brownianFoldUnitIntervalIntegrand hB hBm L hL x σ s t n :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) p =
    brownianElementarySum (brownianFoldUnitIntervalElementary hB hBm L hL x σ s t n) p at ha
  rw [ha]
  change (∑ i : Fin (2 ^ n), brownianElementaryProcess
    (max s (brownianDyadicGrid t n i.castSucc)) (max s (brownianDyadicGrid t n i.succ))
    (brownianFoldUnitCoefficient B L x σ t n i) p) = _
  simp only [brownianElementaryProcess_after, Finset.sum_sub_distrib]
  change (brownianElementarySum (brownianFoldUnitElementary hB hBm L hL x σ t n) p -
    ∑ i : Fin (2 ^ n), (brownianTimePast s).indicator
      (brownianElementaryProcess (brownianDyadicGrid t n i.castSucc)
        (brownianDyadicGrid t n i.succ) (brownianFoldUnitCoefficient B L x σ t n i)) p) = _
  by_cases hp : p ∈ brownianTimePast s
  · simp only [indicator_of_mem hp]
    change brownianElementarySum (brownianFoldUnitElementary hB hBm L hL x σ t n) p -
      brownianElementarySum (brownianFoldUnitElementary hB hBm L hL x σ t n) p =
        (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p -
          (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p
    simp only [sub_self]
  · simp only [indicator_of_notMem hp, Finset.sum_const_zero, sub_zero]
    exact hf.symm

theorem brownianFoldUnitInterval_integral_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (s t : ℝ≥0) (n : ℕ) :
    brownianIntegral hB (brownianFoldUnitIntervalIntegrand hB hBm L hL x σ s t n) =ᵐ[P]
      brownianStepIntegral B (brownianFoldUnitIntervalGrid s t n)
        (brownianFoldUnitCoefficient B L x σ t n) :=
  brownianIntegral_elementarySum_ae hB
    (brownianFoldUnitIntervalElementary hB hBm L hL x σ s t n)

theorem brownianFoldUnitInterval_integral_eq (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (s t : ℝ≥0) (n : ℕ) :
    brownianIntegral hB (brownianFoldUnitIntervalIntegrand hB hBm L hL x σ s t n) =
      brownianIntegral hB (brownianFoldUnitStepIntegrand hB hBm L hL x σ t n) -
        brownianIntegralUpTo hB s (brownianFoldUnitStepIntegrand hB hBm L hL x σ t n) := by
  rw [brownianFoldUnitIntervalIntegrand_eq, map_sub]
  rfl

end TimeTraps.Probability

end
