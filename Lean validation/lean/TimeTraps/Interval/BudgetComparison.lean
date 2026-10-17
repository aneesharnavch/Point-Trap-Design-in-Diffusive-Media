module

public import TimeTraps.Interval.ClosedBudget

@[expose] public section

/-!
Order and translation estimates for the original harmonic budget equation.
The finite weights and normalized budget are fixed throughout each
comparison. Zero weights are permitted, with a nonempty positive support.
-/

namespace TimeTraps.Interval

open scoped BigOperators

variable {ι : Type*}

theorem budget_mono_barrier (s : Finset ι) (p R T : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hRT : ∀ i ∈ s, R i ≤ T i)
    {M : ℝ} (hM : ∀ i ∈ s, T i < M) :
    budget s p R M ≤ budget s p T M := by
  apply Finset.sum_le_sum
  intro i hi
  exact div_le_div_of_nonneg_left (hp i hi) (sub_pos.mpr (hM i hi)) (by linarith [hRT i hi])

theorem budget_lt_barrier (s : Finset ι) (p R T : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hRT : ∀ i ∈ s, R i ≤ T i)
    (hstrict : ∃ i ∈ s, 0 < p i ∧ R i < T i)
    {M : ℝ} (hM : ∀ i ∈ s, T i < M) :
    budget s p R M < budget s p T M := by
  apply Finset.sum_lt_sum
  · intro i hi
    exact div_le_div_of_nonneg_left (hp i hi) (sub_pos.mpr (hM i hi)) (by linarith [hRT i hi])
  · obtain ⟨i, hi, hpi, hri⟩ := hstrict
    exact ⟨i, hi, div_lt_div_of_pos_left hpi (sub_pos.mpr (hM i hi)) (by linarith)⟩

theorem budget_root_mono_barrier (s : Finset ι) (p R T : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    (hRT : ∀ i ∈ s, R i ≤ T i)
    {M N b : ℝ} (hN : ∀ i ∈ s, T i < N)
    (hMroot : budget s p R M = b) (hNroot : budget s p T N = b) : M ≤ N := by
  apply root_le_of_budget_le_nonneg s p R hp hpos
    (fun i hi => (hRT i hi).trans_lt (hN i hi)) hMroot
  exact (budget_mono_barrier s p R T hp hRT hN).trans_eq hNroot

theorem budget_root_lt_barrier (s : Finset ι) (p R T : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i)
    (hRT : ∀ i ∈ s, R i ≤ T i)
    (hstrict : ∃ i ∈ s, 0 < p i ∧ R i < T i)
    {M N b : ℝ} (hN : ∀ i ∈ s, T i < N)
    (hMroot : budget s p R M = b) (hNroot : budget s p T N = b) : M < N := by
  obtain ⟨i, hi, hpi, hri⟩ := hstrict
  apply root_lt_of_budget_lt_nonneg s p R hp ⟨i, hi, hpi⟩
    (fun j hj => (hRT j hj).trans_lt (hN j hj)) hMroot
  exact (budget_lt_barrier s p R T hp hRT ⟨i, hi, hpi, hri⟩ hN).trans_eq hNroot

theorem budget_translate (s : Finset ι) (p R : ι → ℝ) (M η : ℝ) :
    budget s p (fun i => R i + η) (M + η) = budget s p R M := by
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

theorem budget_root_translate (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    {M N b η : ℝ} (hM : ∀ i ∈ s, R i < M)
    (hN : ∀ i ∈ s, R i + η < N)
    (hMroot : budget s p R M = b)
    (hNroot : budget s p (fun i => R i + η) N = b) : N = M + η := by
  apply budget_root_unique_nonneg s p (fun i => R i + η) hp hpos hN
    (fun i hi => by linarith [hM i hi]) hNroot
  rw [budget_translate, hMroot]

theorem budget_root_le_add_of_barrier_le_add (s : Finset ι) (p R T : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    {M N b η : ℝ} (hRT : ∀ i ∈ s, R i ≤ T i + η)
    (hN : ∀ i ∈ s, T i < N)
    (hMroot : budget s p R M = b) (hNroot : budget s p T N = b) : M ≤ N + η := by
  apply budget_root_mono_barrier s p R (fun i => T i + η) hp hpos hRT
    (fun i hi => by linarith [hN i hi]) hMroot
  rw [budget_translate, hNroot]

theorem budget_root_abs_sub_le (s : Finset ι) (p R T : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hpos : ∃ i ∈ s, 0 < p i)
    {M N b ε : ℝ} (hRT : ∀ i ∈ s, |R i - T i| ≤ ε)
    (hM : ∀ i ∈ s, R i < M) (hN : ∀ i ∈ s, T i < N)
    (hMroot : budget s p R M = b) (hNroot : budget s p T N = b) : |M - N| ≤ ε := by
  have hmn := budget_root_le_add_of_barrier_le_add s p R T hp hpos (η := ε)
    (fun i hi => by linarith [(abs_le.mp (hRT i hi)).2]) hN hMroot hNroot
  have hnm := budget_root_le_add_of_barrier_le_add s p T R hp hpos (η := ε)
    (fun i hi => by linarith [(abs_le.mp (hRT i hi)).1]) hM hNroot hMroot
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TimeTraps.Interval
