module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Real.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring

@[expose] public section

/-!
Finite scalar-budget lemmas used in Section 4 of `preprint/main.tex`.
These establish only the displayed algebraic implications. Construction of
the barriers, root existence, and the connection to physical designs are
separate proof obligations recorded in the formalization plan.
-/

namespace TimeTraps.Interval

open scoped BigOperators

variable {ι : Type*}

/-- The normalized reactivity required to attain a specified cell height. -/
noncomputable def budget (s : Finset ι) (p R : ι → ℝ) (M : ℝ) : ℝ :=
  ∑ i ∈ s, p i / (M - R i)

/-- Increasing the height strictly decreases the budget for nonempty positive cells. -/
theorem budget_strict_decreasing (s : Finset ι) (hs : s.Nonempty)
    (p R : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i)
    {M₁ M₂ : ℝ} (hR : ∀ i ∈ s, R i < M₁) (hM : M₁ < M₂) :
    budget s p R M₂ < budget s p R M₁ := by
  unfold budget
  have hterm : ∀ i ∈ s, p i / (M₂ - R i) < p i / (M₁ - R i) := by
    intro i hi
    exact div_lt_div_of_pos_left (hp i hi) (sub_pos.mpr (hR i hi)) (by linarith)
  obtain ⟨i, hi⟩ := hs
  exact Finset.sum_lt_sum (fun j hj => (hterm j hj).le) ⟨i, hi, hterm i hi⟩

/-- The root comparison used to pass from an arbitrary design to its partition. -/
theorem root_le_of_budget_le (s : Finset ι) (hs : s.Nonempty)
    (p R : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i)
    {M T b : ℝ} (hM : ∀ i ∈ s, R i < M)
    (hT : budget s p R T = b) (hb : budget s p R M ≤ b) :
    T ≤ M := by
  by_contra h
  have hlt : M < T := lt_of_not_ge h
  have hdec := budget_strict_decreasing s hs p R hp hM hlt
  rw [hT] at hdec
  exact (not_lt_of_ge hb) hdec

/-- A root above all cell barriers is unique. -/
theorem budget_root_unique (s : Finset ι) (hs : s.Nonempty)
    (p R : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i)
    {M T b : ℝ} (hM : ∀ i ∈ s, R i < M) (hT : ∀ i ∈ s, R i < T)
    (hMb : budget s p R M = b) (hTb : budget s p R T = b) :
    M = T := by
  apply le_antisymm
  · exact root_le_of_budget_le s hs p R hp hT hMb hTb.le
  · exact root_le_of_budget_le s hs p R hp hM hTb hMb.le

/-- The reconstruction formula produces a positive strength. -/
theorem reconstructed_strength_pos {S p M R : ℝ}
    (hS : 0 < S) (hp : 0 < p) (hR : R < M) :
    0 < S * p / (M - R) :=
  div_pos (mul_pos hS hp) (sub_pos.mpr hR)

/-- A normalized budget root reconstructs the exact physical strength budget. -/
theorem reconstructed_strength_sum (s : Finset ι) (p R : ι → ℝ)
    {S K M : ℝ} (hS : S ≠ 0) (hroot : budget s p R M = K / S) :
    (∑ i ∈ s, S * p i / (M - R i)) = K := by
  calc
    (∑ i ∈ s, S * p i / (M - R i)) = S * budget s p R M := by
      simp only [budget, Finset.mul_sum, mul_div_assoc]
    _ = S * (K / S) := by rw [hroot]
    _ = K := by field_simp

end TimeTraps.Interval
