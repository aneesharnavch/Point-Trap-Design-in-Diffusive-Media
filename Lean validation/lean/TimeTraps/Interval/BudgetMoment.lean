module

public import TimeTraps.Interval.BudgetRoot
public import TimeTraps.Analysis.WeightedVariance

@[expose] public section

/-!
The arithmetic--harmonic lower bound for a unit-mass budget root, including
its exact equality condition. It follows from the proved weighted-square
identity with weights p_i/(M-R_i), rather than from numerical root estimates.
-/

namespace TimeTraps.Interval

open TimeTraps.Analysis
open scoped BigOperators

theorem budget_root_mean_barrier_bound {ι : Type*} (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) (hsum : (∑ i ∈ s, p i) = 1)
    {b M : ℝ} (hb : 0 < b) (hM : ∀ i ∈ s, R i < M)
    (hroot : budget s p R M = b) :
    1 / b + (∑ i ∈ s, p i * R i) ≤ M ∧
      (M = 1 / b + (∑ i ∈ s, p i * R i) ↔
        ∀ i ∈ s, 0 < p i → M - R i = 1 / b) := by
  have hd : ∀ i ∈ s, 0 < M - R i := fun i hi => sub_pos.mpr (hM i hi)
  have hx : (∑ i ∈ s, (p i / (M - R i)) * (M - R i)) = 1 := by
    calc
      _ = ∑ i ∈ s, p i := Finset.sum_congr rfl (fun i hi => div_mul_cancel₀ _ (ne_of_gt (hd i hi)))
      _ = 1 := hsum
  have hxx : (∑ i ∈ s, (p i / (M - R i)) * (M - R i) ^ 2) =
      M - ∑ i ∈ s, p i * R i := by
    calc
      _ = ∑ i ∈ s, p i * (M - R i) := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [ne_of_gt (hd i hi)]
      _ = _ := by
        simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hsum, one_mul]
  have h := weighted_second_moment_bound s (fun i => p i / (M - R i)) (fun i => M - R i)
    hb hroot hx (fun i hi => div_nonneg (hp i hi) (hd i hi).le)
  rw [hxx, one_pow] at h
  refine ⟨by linarith [h.1], ?_⟩
  constructor
  · intro he i hi hpi
    exact h.2.mp (by linarith) i hi (div_pos hpi (hd i hi))
  · intro he
    have heq := h.2.mpr (fun i hi hwi => he i hi (by
      have ht := mul_pos hwi (hd i hi)
      rwa [div_mul_cancel₀ _ (ne_of_gt (hd i hi))] at ht))
    linarith

end TimeTraps.Interval
