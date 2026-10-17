module

public import TimeTraps.Interval.Budget
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Topology.Algebra.Field
public import Mathlib.Topology.Instances.Real.Lemmas
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
Existence and quantitative bounds for the scalar equation in
`preprint/main.tex`, equation `eq:harmonic-root`. The weights and barriers
are arbitrary finite real data; identifying them with a physical partition
is a separate obligation.
-/

namespace TimeTraps.Interval

open scoped BigOperators

variable {ι : Type*}

theorem budget_continuousOn (s : Finset ι) (p R : ι → ℝ) :
    ContinuousOn (budget s p R) {M | ∀ i ∈ s, R i < M} := by
  unfold budget
  apply continuousOn_finsetSum
  intro i hi
  exact continuousOn_const.div (continuousOn_id.sub continuousOn_const)
    (fun M hM => ne_of_gt (sub_pos.mpr (hM i hi)))

/-- A positive target budget has exactly one root above all barriers. -/
theorem budget_root_existsUnique (s : Finset ι) (hs : s.Nonempty)
    (p R : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i)
    {b : ℝ} (hb : 0 < b) :
    ∃! M : ℝ, (∀ i ∈ s, R i < M) ∧ budget s p R M = b := by
  obtain ⟨j, hj, hmax⟩ := s.exists_max_image R hs
  let P := ∑ i ∈ s, p i
  have hP : 0 < P := Finset.sum_pos hp hs
  have hpP : p j ≤ P := Finset.single_le_sum (fun i hi => (hp i hi).le) hj
  let lo := R j + p j / (2 * b)
  let upper := R j + P / b
  have hlo : ∀ i ∈ s, R i < lo := by
    intro i hi
    have := div_pos (hp j hj) (mul_pos (by norm_num : (0 : ℝ) < 2) hb)
    dsimp [lo]
    linarith [hmax i hi]
  have horder : lo ≤ upper := by
    dsimp [lo, upper]
    apply add_le_add le_rfl
    apply (div_le_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 2) hb)).mpr
    have : P / b * (2 * b) = 2 * P := by field_simp
    rw [this]
    linarith
  have hloBudget : b ≤ budget s p R lo := by
    have hsingle : p j / (lo - R j) ≤ budget s p R lo :=
      Finset.single_le_sum
        (fun i hi => (div_pos (hp i hi) (sub_pos.mpr (hlo i hi))).le) hj
    have hvalue : p j / (lo - R j) = 2 * b := by
      dsimp [lo]
      rw [add_sub_cancel_left]
      field_simp [ne_of_gt (hp j hj), ne_of_gt hb]
    rw [hvalue] at hsingle
    linarith
  have hhiBudget : budget s p R upper ≤ b := by
    calc
      budget s p R upper ≤ ∑ i ∈ s, p i / (P / b) := by
        apply Finset.sum_le_sum
        intro i hi
        apply div_le_div_of_nonneg_left (hp i hi).le (div_pos hP hb)
        dsimp [upper]
        linarith [hmax i hi]
      _ = P / (P / b) := by rw [← Finset.sum_div]
      _ = b := by field_simp
  have hc : ContinuousOn (budget s p R) (Set.Icc lo upper) :=
    (budget_continuousOn s p R).mono (fun M hM i hi => lt_of_lt_of_le (hlo i hi) hM.1)
  obtain ⟨M, hM, hroot⟩ := intermediate_value_Icc' horder hc ⟨hhiBudget, hloBudget⟩
  refine ⟨M, ⟨fun i hi => lt_of_lt_of_le (hlo i hi) hM.1, hroot⟩, ?_⟩
  intro T hT
  exact budget_root_unique s hs p R hp hT.1
    (fun i hi => lt_of_lt_of_le (hlo i hi) hM.1) hT.2 hroot

/-- Each individual cell gives a lower bound on any root. -/
theorem budget_root_cell_lower (s : Finset ι) (p R : ι → ℝ)
    (hp : ∀ i ∈ s, 0 ≤ p i) {b M : ℝ} (hb : 0 < b)
    (hM : ∀ i ∈ s, R i < M) (hroot : budget s p R M = b)
    {j : ι} (hj : j ∈ s) : R j + p j / b ≤ M := by
  have hsingle : p j / (M - R j) ≤ b := by
    rw [← hroot]
    exact Finset.single_le_sum (fun i hi => div_nonneg (hp i hi) (sub_pos.mpr (hM i hi)).le) hj
  have := (div_le_iff₀ (sub_pos.mpr (hM j hj))).mp hsingle
  have : p j / b ≤ M - R j := (div_le_iff₀ hb).mpr (by nlinarith)
  linarith

/-- The maximum barrier plus total weight divided by the budget bounds the root. -/
theorem budget_root_upper (s : Finset ι) (hs : s.Nonempty)
    (p R : ι → ℝ) (hp : ∀ i ∈ s, 0 < p i)
    {b M Rmax : ℝ} (hb : 0 < b) (hR : ∀ i ∈ s, R i ≤ Rmax)
    (hroot : budget s p R M = b) :
    M ≤ Rmax + (∑ i ∈ s, p i) / b := by
  let P := ∑ i ∈ s, p i
  have hP : 0 < P := Finset.sum_pos hp hs
  have hupper : ∀ i ∈ s, R i < Rmax + P / b := by
    intro i hi
    linarith [hR i hi, div_pos hP hb]
  apply root_le_of_budget_le s hs p R hp hupper hroot
  calc
    budget s p R (Rmax + P / b) ≤ ∑ i ∈ s, p i / (P / b) := by
      apply Finset.sum_le_sum
      intro i hi
      exact div_le_div_of_nonneg_left (hp i hi).le (div_pos hP hb) (by linarith [hR i hi])
    _ = P / (P / b) := by rw [← Finset.sum_div]
    _ = b := by field_simp

end TimeTraps.Interval
