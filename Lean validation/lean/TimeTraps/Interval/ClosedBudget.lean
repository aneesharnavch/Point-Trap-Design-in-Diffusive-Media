module

public import TimeTraps.Interval.BudgetRoot

@[expose] public section

/-!
The scalar budget on the closed partition simplex. Zero-width cells retain
their indices and contribute zero. Existence is reduced to the positive
support, and the root is proved positive and above every barrier.
-/

namespace TimeTraps.Interval

open scoped BigOperators

variable {ι : Type*}

theorem budget_strict_decreasing_nonneg (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    {M₁ M₂ : ℝ} (hR : ∀ i ∈ s, R i < M₁) (hM : M₁ < M₂) :
    budget s p R M₂ < budget s p R M₁ := by
  apply Finset.sum_lt_sum
  · intro i hi
    exact div_le_div_of_nonneg_left (hp i hi) (sub_pos.mpr (hR i hi)) (by linarith)
  · obtain ⟨i, hi, hpi⟩ := hpos
    exact ⟨i, hi, div_lt_div_of_pos_left hpi (sub_pos.mpr (hR i hi)) (by linarith)⟩

theorem root_le_of_budget_le_nonneg (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    {M T b : ℝ} (hM : ∀ i ∈ s, R i < M)
    (hT : budget s p R T = b) (hb : budget s p R M ≤ b) : T ≤ M := by
  by_contra h
  have hd := budget_strict_decreasing_nonneg s p R hp hpos hM (lt_of_not_ge h)
  rw [hT] at hd
  exact (not_lt_of_ge hb) hd

theorem root_lt_of_budget_lt_nonneg (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    {M T b : ℝ} (hM : ∀ i ∈ s, R i < M)
    (hT : budget s p R T = b) (hb : budget s p R M < b) : T < M := by
  have hle := root_le_of_budget_le_nonneg s p R hp hpos hM hT hb.le
  apply lt_of_le_of_ne hle
  intro he
  rw [← he, hT] at hb
  exact lt_irrefl _ hb

theorem lt_root_of_lt_budget_nonneg (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    {M T b : ℝ} (hT : ∀ i ∈ s, R i < T)
    (hroot : budget s p R T = b) (hb : b < budget s p R M) : M < T := by
  by_contra hn
  rcases (le_of_not_gt hn).lt_or_eq with hlt | he
  · have hd := budget_strict_decreasing_nonneg s p R hp hpos hT hlt
    rw [hroot] at hd
    exact (not_lt_of_ge hd.le) hb
  · rw [← he, hroot] at hb
    exact lt_irrefl _ hb

theorem budget_root_unique_nonneg (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    {M T b : ℝ} (hM : ∀ i ∈ s, R i < M) (hT : ∀ i ∈ s, R i < T)
    (hMb : budget s p R M = b) (hTb : budget s p R T = b) : M = T := by
  exact le_antisymm (root_le_of_budget_le_nonneg s p R hp hpos hT hMb hTb.le)
    (root_le_of_budget_le_nonneg s p R hp hpos hM hTb hMb.le)

theorem budget_positive_support (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (M : ℝ) :
    budget (s.filter (fun i => 0 < p i)) p R M = budget s p R M := by
  classical
  apply Finset.sum_subset (Finset.filter_subset _ s)
  intro i hi hn
  have hn' : ¬0 < p i := by simpa only [Finset.mem_filter, hi, true_and] using hn
  have hz : p i = 0 := le_antisymm (le_of_not_gt hn') (hp i hi)
  simp only [hz, zero_div]

/-- The zero-width convention agrees with the root on positive cells and
still places the root strictly above every barrier, including zero cells. -/
theorem budget_root_existsUnique_nonneg (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    (hR : ∀ i ∈ s, 0 ≤ R i) (hzero : ∀ i ∈ s, p i = 0 → R i = 0)
    {b : ℝ} (hb : 0 < b) :
    ∃! M : ℝ, (∀ i ∈ s, R i < M) ∧ budget s p R M = b := by
  classical
  let t := s.filter (fun i => 0 < p i)
  obtain ⟨j, hj, hpj⟩ := hpos
  have hjt : j ∈ t := Finset.mem_filter.mpr ⟨hj, hpj⟩
  obtain ⟨M, hM, _⟩ := budget_root_existsUnique t ⟨j, hjt⟩ p R
    (fun i hi => (Finset.mem_filter.mp hi).2) hb
  have hMp : 0 < M := (hR j hj).trans_lt (hM.1 j hjt)
  have hMa : ∀ i ∈ s, R i < M := by
    intro i hi
    by_cases hpi : 0 < p i
    · exact hM.1 i (Finset.mem_filter.mpr ⟨hi, hpi⟩)
    · rw [hzero i hi (le_antisymm (le_of_not_gt hpi) (hp i hi))]
      exact hMp
  have hMb : budget s p R M = b := by
    rw [← budget_positive_support s p R hp M]
    exact hM.2
  refine ⟨M, ⟨hMa, hMb⟩, ?_⟩
  intro T hT
  exact budget_root_unique_nonneg s p R hp ⟨j, hj, hpj⟩ hT.1 hMa hT.2 hMb

theorem budget_root_lower_nonneg (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    (hR : ∀ i ∈ s, 0 ≤ R i) {b M : ℝ} (hb : 0 < b)
    (hM : ∀ i ∈ s, R i < M) (hroot : budget s p R M = b) :
    (∑ i ∈ s, p i) / b ≤ M := by
  obtain ⟨j, hj, _⟩ := hpos
  have hMp : 0 < M := (hR j hj).trans_lt (hM j hj)
  have hs : (∑ i ∈ s, p i) / M ≤ b := by
    rw [← hroot, Finset.sum_div]
    apply Finset.sum_le_sum
    intro i hi
    exact div_le_div_of_nonneg_left (hp i hi) (sub_pos.mpr (hM i hi)) (by linarith [hR i hi])
  apply (div_le_iff₀ hb).mpr
  have := (div_le_iff₀ hMp).mp hs
  linarith

theorem budget_root_upper_nonneg (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    {b M Rmax : ℝ} (hb : 0 < b) (hR : ∀ i ∈ s, R i ≤ Rmax)
    (hroot : budget s p R M = b) :
    M ≤ Rmax + (∑ i ∈ s, p i) / b := by
  let P := ∑ i ∈ s, p i
  have hP : 0 < P := (Finset.sum_pos_iff_of_nonneg hp).mpr hpos
  have hupper : ∀ i ∈ s, R i < Rmax + P / b := by
    intro i hi
    linarith [hR i hi, div_pos hP hb]
  apply root_le_of_budget_le_nonneg s p R hp hpos hupper hroot
  calc
    budget s p R (Rmax + P / b) ≤ ∑ i ∈ s, p i / (P / b) := by
      apply Finset.sum_le_sum
      intro i hi
      exact div_le_div_of_nonneg_left (hp i hi) (div_pos hP hb) (by linarith [hR i hi])
    _ = P / (P / b) := by rw [← Finset.sum_div]
    _ = b := by field_simp

end TimeTraps.Interval
