module

public import TimeTraps.Probability.ContinuousMonotoneQuadraticVariation

@[expose] public section

/-! Literal left-weighted finite dyadic increments and their algebra.
All identities hold for arbitrary real paths, without continuity,
probabilistic, or variation assumptions. -/

namespace TimeTraps.Probability

open Set
open scoped NNReal

noncomputable def dyadicWeightedIncrement (H q : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i : Fin (2 ^ n), H (brownianDyadicGrid T n i.castSucc) *
    (q (brownianDyadicGrid T n i.succ) - q (brownianDyadicGrid T n i.castSucc))

theorem dyadicWeightedIncrement_add (H q r : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    dyadicWeightedIncrement H (fun t => q t + r t) T n =
      dyadicWeightedIncrement H q T n + dyadicWeightedIncrement H r T n := by
  unfold dyadicWeightedIncrement
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dyadicWeightedIncrement_sub (H q r : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    dyadicWeightedIncrement H (fun t => q t - r t) T n =
      dyadicWeightedIncrement H q T n - dyadicWeightedIncrement H r T n := by
  unfold dyadicWeightedIncrement
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dyadicWeightedIncrement_const_mul (H q : ℝ≥0 → ℝ) (c : ℝ) (T : ℝ≥0) (n : ℕ) :
    dyadicWeightedIncrement H (fun t => c * q t) T n = c * dyadicWeightedIncrement H q T n := by
  unfold dyadicWeightedIncrement
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dyadicWeightedIncrement_sum {ι : Type*} [Fintype ι]
    (H : ℝ≥0 → ℝ) (q : ι → ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    dyadicWeightedIncrement H (fun t => ∑ j, q j t) T n =
      ∑ j, dyadicWeightedIncrement H (q j) T n := by
  simp only [dyadicWeightedIncrement, ← Finset.sum_sub_distrib, Finset.mul_sum]
  exact Finset.sum_comm

theorem dyadicWeightedIncrement_const (H : ℝ≥0 → ℝ) (c : ℝ) (T : ℝ≥0) (n : ℕ) :
    dyadicWeightedIncrement H (fun _ => c) T n = 0 := by
  simp only [dyadicWeightedIncrement, sub_self, mul_zero, Finset.sum_const_zero]

theorem dyadicWeightedIncrement_weight_add (H G q : ℝ≥0 → ℝ) (T : ℝ≥0) (n : ℕ) :
    dyadicWeightedIncrement (fun t => H t + G t) q T n =
      dyadicWeightedIncrement H q T n + dyadicWeightedIncrement G q T n := by
  simp only [dyadicWeightedIncrement, add_mul, Finset.sum_add_distrib]

theorem dyadicWeightedIncrement_weight_const_mul (H q : ℝ≥0 → ℝ)
    (c : ℝ) (T : ℝ≥0) (n : ℕ) :
    dyadicWeightedIncrement (fun t => c * H t) q T n = c * dyadicWeightedIncrement H q T n := by
  simp only [dyadicWeightedIncrement, mul_assoc, Finset.mul_sum]

theorem dyadicWeightedIncrement_congr {H G q r : ℝ≥0 → ℝ} {T : ℝ≥0}
    (hH : EqOn H G (Icc 0 T)) (hq : EqOn q r (Icc 0 T)) (n : ℕ) :
    dyadicWeightedIncrement H q T n = dyadicWeightedIncrement G r T n := by
  apply Finset.sum_congr rfl
  intro i _
  rw [hH (brownianDyadicGrid_mem_Icc T n i.castSucc),
    hq (brownianDyadicGrid_mem_Icc T n i.succ), hq (brownianDyadicGrid_mem_Icc T n i.castSucc)]

theorem dyadicWeightedIncrement_congr_of_sub_const (H q r : ℝ≥0 → ℝ)
    (c : ℝ) {T : ℝ≥0} (hq : ∀ t ∈ Icc 0 T, q t - c = r t) (n : ℕ) :
    dyadicWeightedIncrement H q T n = dyadicWeightedIncrement H r T n := by
  apply Finset.sum_congr rfl
  intro i _
  have hl := hq _ (brownianDyadicGrid_mem_Icc T n i.castSucc)
  have hr := hq _ (brownianDyadicGrid_mem_Icc T n i.succ)
  have he : q (brownianDyadicGrid T n i.succ) - q (brownianDyadicGrid T n i.castSucc) =
      r (brownianDyadicGrid T n i.succ) - r (brownianDyadicGrid T n i.castSucc) := by linarith
  rw [he]

end TimeTraps.Probability
