module

public import TimeTraps.Probability.BrownianIntegralSquareFinite
public import Mathlib.Order.Interval.Set.Union

@[expose] public section

/-! The actual left-endpoint step process on dyadic cells, including
cell coverage, uniqueness and the zero value outside (0,T]. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem brownianDyadicGrid_cell (T : ℝ≥0) (n : ℕ) {r : ℝ} (hr : r ∈ Ioc 0 T.val) :
    ∃ i : Fin (2 ^ n), r ∈ Ioc (brownianDyadicGrid T n i.castSucc).val
      (brownianDyadicGrid T n i.succ).val := by
  let a : ℕ → ℝ := fun k => k * T.val / (2 : ℝ) ^ n
  have h0 : a 0 = 0 := by simp [a]
  have hT : a (2 ^ n) = T.val := by
    dsimp [a]
    rw [Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have hm : r ∈ Ioc (a 0) (a (2 ^ n)) := by simpa only [h0, hT] using hr
  have hu := Ioc_subset_biUnion_Ioc (2 ^ n) a hm
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hu
  obtain ⟨hi, hs⟩ := Set.mem_iUnion.mp hi
  exact ⟨⟨i, Finset.mem_range.mp hi⟩, hs⟩

theorem brownianDyadicGrid_cell_unique (T : ℝ≥0) (n : ℕ) {r : ℝ} {i j : Fin (2 ^ n)}
    (hi : r ∈ Ioc (brownianDyadicGrid T n i.castSucc).val (brownianDyadicGrid T n i.succ).val)
    (hj : r ∈ Ioc (brownianDyadicGrid T n j.castSucc).val (brownianDyadicGrid T n j.succ).val) :
    i = j := by
  apply le_antisymm
  · by_contra hn
    have hji : j < i := lt_of_not_ge hn
    have hidx : j.succ ≤ i.castSucc := Nat.succ_le_of_lt hji
    have hg : (brownianDyadicGrid T n j.succ).val ≤
        (brownianDyadicGrid T n i.castSucc).val := brownianDyadicGrid_monotone T n hidx
    exact (hi.1.trans_le (hj.2.trans hg)).false
  · by_contra hn
    have hij : i < j := lt_of_not_ge hn
    have hidx : i.succ ≤ j.castSucc := Nat.succ_le_of_lt hij
    have hg : (brownianDyadicGrid T n i.succ).val ≤
        (brownianDyadicGrid T n j.castSucc).val := brownianDyadicGrid_monotone T n hidx
    exact (hj.1.trans_le (hi.2.trans hg)).false

variable {Ω : Type*}

noncomputable def brownianSquareStepProcess (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) : ℝ :=
  ∑ i : Fin (2 ^ n), brownianElementaryProcess (brownianDyadicGrid T n i.castSucc)
    (brownianDyadicGrid T n i.succ) (B (brownianDyadicGrid T n i.castSucc)) p

theorem brownianSquareStepProcess_cell (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ)
    {r : ℝ} (ω : Ω) (i : Fin (2 ^ n))
    (hr : r ∈ Ioc (brownianDyadicGrid T n i.castSucc).val (brownianDyadicGrid T n i.succ).val) :
    brownianSquareStepProcess B T n (r, ω) = B (brownianDyadicGrid T n i.castSucc) ω := by
  classical
  rw [brownianSquareStepProcess, Finset.sum_eq_single i]
  · simp only [brownianElementaryProcess, brownianIntervalIndicator, Set.indicator_of_mem hr, one_mul]
  · intro j _ hji
    have hj : r ∉ Ioc (brownianDyadicGrid T n j.castSucc).val (brownianDyadicGrid T n j.succ).val :=
      fun hj => hji (brownianDyadicGrid_cell_unique T n hj hr)
    simp only [brownianElementaryProcess, brownianIntervalIndicator, Set.indicator_of_notMem hj, zero_mul]
  · simp

theorem brownianSquareStepProcess_outside (B : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (n : ℕ)
    {r : ℝ} (ω : Ω) (hr : r ∉ Ioc 0 T.val) : brownianSquareStepProcess B T n (r, ω) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : r ∉ Ioc (brownianDyadicGrid T n i.castSucc).val (brownianDyadicGrid T n i.succ).val := by
    intro hi
    apply hr
    refine ⟨(brownianDyadicGrid T n i.castSucc).coe_nonneg.trans_lt hi.1, ?_⟩
    have hg : (brownianDyadicGrid T n i.succ).val ≤ T.val := by
      exact (brownianDyadicGrid_monotone T n (Fin.le_last i.succ)).trans_eq (brownianDyadicGrid_last T n)
    exact hi.2.trans hg
  simp only [brownianElementaryProcess, brownianIntervalIndicator, Set.indicator_of_notMem hi, zero_mul]

variable {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSquareStepIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) :
    (brownianSquareStepIntegrand hB hBm T n : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      brownianSquareStepProcess B T n :=
  brownianElementarySumIntegrand_coe (brownianSquareElementary hB hBm T n)

end TimeTraps.Probability
