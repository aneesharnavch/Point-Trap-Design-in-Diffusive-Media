module

public import TimeTraps.Analysis.WeightedVariance
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
An exact cubic expansion gives the length inequality and its equality case.
All variables are real and the finite family is arbitrary; no numerical
search or approximation is used.
-/

namespace TimeTraps.Analysis

open scoped BigOperators

variable {ι : Type*}

theorem weighted_cubic_identity (s : Finset ι) (w x : ι → ℝ)
    {W L : ℝ} (hW : W ≠ 0) (hw : ∑ i ∈ s, w i = W)
    (hx : ∑ i ∈ s, w i * x i = L) :
    (∑ i ∈ s, w i * (x i - L / W) ^ 2 * (x i + 2 * (L / W))) =
      (∑ i ∈ s, w i * x i ^ 3) - L ^ 3 / W ^ 2 := by
  calc
    _ = ∑ i ∈ s, (w i * x i ^ 3 - 3 * (L / W) ^ 2 * (w i * x i) +
        2 * (L / W) ^ 3 * w i) := by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, hw, hx]
      field_simp
      ring

theorem weighted_cubic_bound (s : Finset ι) (w x : ι → ℝ)
    {W L : ℝ} (hW : 0 < W) (hL : 0 < L) (hw : ∑ i ∈ s, w i = W)
    (hx : ∑ i ∈ s, w i * x i = L) (hwpos : ∀ i ∈ s, 0 < w i)
    (hxnonneg : ∀ i ∈ s, 0 ≤ x i) :
    L ^ 3 / W ^ 2 ≤ (∑ i ∈ s, w i * x i ^ 3) ∧
      ((∑ i ∈ s, w i * x i ^ 3) = L ^ 3 / W ^ 2 ↔ ∀ i ∈ s, x i = L / W) := by
  have hid := weighted_cubic_identity s w x (ne_of_gt hW) hw hx
  have hc : 0 < L / W := div_pos hL hW
  have hp : ∀ i ∈ s, 0 < x i + 2 * (L / W) := by
    intro i hi
    linarith [hxnonneg i hi]
  have hn : ∀ i ∈ s, 0 ≤ w i * (x i - L / W) ^ 2 * (x i + 2 * (L / W)) :=
    fun i hi => mul_nonneg (mul_nonneg (hwpos i hi).le (sq_nonneg _)) (hp i hi).le
  have hs := Finset.sum_nonneg hn
  refine ⟨by linarith, ?_⟩
  constructor
  · intro heq i hi
    have hz : (∑ i ∈ s, w i * (x i - L / W) ^ 2 * (x i + 2 * (L / W))) = 0 := by
      linarith
    have hi0 := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hz i hi
    have hm0 := (mul_eq_zero.mp hi0).resolve_right (ne_of_gt (hp i hi))
    have hsq := (mul_eq_zero.mp hm0).resolve_left (ne_of_gt (hwpos i hi))
    exact sub_eq_zero.mp (sq_eq_zero_iff.mp hsq)
  · intro heq
    have hz : (∑ i ∈ s, w i * (x i - L / W) ^ 2 * (x i + 2 * (L / W))) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [heq i hi, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, zero_mul]
    linarith

/-- The cubic length bound, with equality exactly at lengths proportional to
the positive scales. Zero trial lengths are also allowed in this inequality. -/
theorem cubic_length_bound (s : Finset ι) (scale length : ι → ℝ)
    {S L : ℝ} (hS : 0 < S) (hL : 0 < L) (hsum : ∑ i ∈ s, scale i = S)
    (hlen : ∑ i ∈ s, length i = L) (hscale : ∀ i ∈ s, 0 < scale i)
    (hpos : ∀ i ∈ s, 0 ≤ length i) :
    L ^ 3 / S ^ 2 ≤ (∑ i ∈ s, length i ^ 3 / scale i ^ 2) ∧
      ((∑ i ∈ s, length i ^ 3 / scale i ^ 2) = L ^ 3 / S ^ 2 ↔
        ∀ i ∈ s, length i = L * scale i / S) := by
  have hx : (∑ i ∈ s, scale i * (length i / scale i)) = L := by
    calc
      _ = ∑ i ∈ s, length i := by
        apply Finset.sum_congr rfl
        intro i hi
        field_simp [ne_of_gt (hscale i hi)]
      _ = L := hlen
  have hb := weighted_cubic_bound s scale (fun i => length i / scale i)
    hS hL hsum hx hscale (fun i hi => div_nonneg (hpos i hi) (hscale i hi).le)
  have ht : (∑ i ∈ s, scale i * (length i / scale i) ^ 3) =
      ∑ i ∈ s, length i ^ 3 / scale i ^ 2 := by
    apply Finset.sum_congr rfl
    intro i hi
    field_simp [ne_of_gt (hscale i hi)]
  rw [ht] at hb
  refine ⟨hb.1, hb.2.trans ?_⟩
  apply forall_congr'
  intro i
  apply forall_congr'
  intro hi
  rw [div_eq_iff (ne_of_gt (hscale i hi))]
  rw [show L / S * scale i = L * scale i / S by ring]

end TimeTraps.Analysis
