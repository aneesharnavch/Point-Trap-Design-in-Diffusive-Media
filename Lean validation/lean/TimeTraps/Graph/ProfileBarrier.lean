module

public import TimeTraps.Graph.ProfileCostIdentity
public import TimeTraps.Graph.ProfileMinimum

@[expose] public section

/-! Sharp local variable-profile cost bounds, including exterior flux levels
and the two distinct passive-tip orientations. -/

namespace TimeTraps.Graph

open Set TimeTraps.Interval

variable {W : CellWeight} {α m : ℝ} {y : ℝ → ℝ}

theorem ProfileEquation.cost_gt_left (h : ProfileEquation W α y)
    (hm : 0 < m) (hy : 0 ≤ y 0) (hα : α < 0) :
    profileCost W m 0 < profileIntegralCost W m α y := by
  have hA := profile_moment_bounds W
  have hB : 0 < W.primitive 1 := hA.1.trans hA.2
  have hf : 0 < W.moment 1 + W.primitive 1 - α * W.primitive 1 := by
    nlinarith [mul_neg_of_neg_of_pos hα hB]
  have hp : 0 < y 0 - α * (W.moment 1 + W.primitive 1 - α * W.primitive 1) := by
    nlinarith [mul_neg_of_neg_of_pos hα hf]
  have he := h.cost_left_difference m
  have hpos := mul_pos hm hp
  linarith

theorem ProfileEquation.cost_gt_right (h : ProfileEquation W α y)
    (hm : 0 < m) (hy : 0 ≤ y 1) (hα : 1 < α) :
    profileCost W m 1 < profileIntegralCost W m α y := by
  have hA := profile_moment_bounds W
  have hB : 0 < W.primitive 1 := hA.1.trans hA.2
  have hf : 0 < (α + 1) * W.primitive 1 - W.moment 1 := by
    nlinarith [mul_pos (show 0 < α by linarith) hB]
  have hp : 0 < y 1 + (α - 1) * ((α + 1) * W.primitive 1 - W.moment 1) :=
    add_pos_of_nonneg_of_pos hy (mul_pos (sub_pos.mpr hα) hf)
  have he := h.cost_right_difference m
  have hpos := mul_pos hm hp
  linarith

theorem ProfileEquation.minimum_le_cost (h : ProfileEquation W α y)
    (hm : 0 < m) (hy : ∀ z ∈ Icc (0 : ℝ) 1, 0 ≤ y z) :
    profileMinimum W m ≤ profileIntegralCost W m α y := by
  by_cases hα : α ∈ Icc (0 : ℝ) 1
  · have hb := (profileCost_minimum W hm).2 ⟨α, hα, rfl⟩
    rw [h.cost_interior m hα]
    linarith [mul_nonneg hm.le (hy α hα)]
  · have hout : α < 0 ∨ 1 < α := by
      simp only [mem_Icc, not_and_or, not_le] at hα
      exact hα
    rcases hout with hl | hr
    · exact ((profileCost_minimum W hm).2 ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩).trans
        (h.cost_gt_left hm (hy 0 ⟨le_rfl, zero_le_one⟩) hl).le
    · exact ((profileCost_minimum W hm).2 ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩).trans
        (h.cost_gt_right hm (hy 1 ⟨zero_le_one, le_rfl⟩) hr).le

theorem ProfileEquation.cost_eq_minimum_iff (h : ProfileEquation W α y)
    (hm : 0 < m) (hy : ∀ z ∈ Icc (0 : ℝ) 1, 0 ≤ y z) :
    profileIntegralCost W m α y = profileMinimum W m ↔
      α = profileMinimizer W ∧ y α = 0 := by
  constructor
  · intro he
    have hα : α ∈ Icc (0 : ℝ) 1 := by
      constructor
      · by_contra hn
        have hl := h.cost_gt_left hm (hy 0 ⟨le_rfl, zero_le_one⟩) (lt_of_not_ge hn)
        have hb := (profileCost_minimum W hm).2 ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩
        linarith
      · by_contra hn
        have hr := h.cost_gt_right hm (hy 1 ⟨zero_le_one, le_rfl⟩) (lt_of_not_ge hn)
        have hb := (profileCost_minimum W hm).2 ⟨1, ⟨zero_le_one, le_rfl⟩, rfl⟩
        linarith
    have hb := (profileCost_minimum W hm).2 ⟨α, hα, rfl⟩
    have hi := h.cost_interior m hα
    have hn := mul_nonneg hm.le (hy α hα)
    have hc : profileCost W m α = profileMinimum W m := by linarith
    refine ⟨(profileCost_eq_minimum_iff W hm hα).mp hc, ?_⟩
    have hz : m * y α = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hm)
  · rintro ⟨rfl, hy0⟩
    rw [h.cost_interior m (Ioo_subset_Icc_self (profileMinimizer_mem W)), hy0, mul_zero, zero_add]
    rfl

theorem ProfileEquation.passive_tail_bound {y : ℝ → ℝ} (h : ProfileEquation W 0 y)
    (hm : 0 < m) (hy : 0 ≤ y 0) :
    m * W.moment 1 ≤ profileIntegralCost W m 0 y := by
  rw [h.cost_passive_tail]
  linarith [mul_nonneg hm.le hy]

theorem ProfileEquation.passive_head_bound {y : ℝ → ℝ} (h : ProfileEquation W 1 y)
    (hm : 0 < m) (hy : 0 ≤ y 1) :
    m * (W.primitive 1 - W.moment 1) ≤ profileIntegralCost W m 1 y := by
  rw [h.cost_passive_head]
  linarith [mul_nonneg hm.le hy]

theorem ProfileEquation.passive_tail_eq_iff {y : ℝ → ℝ} (h : ProfileEquation W 0 y)
    (hm : 0 < m) : profileIntegralCost W m 0 y = m * W.moment 1 ↔ y 0 = 0 := by
  rw [h.cost_passive_tail]
  constructor
  · intro he
    have hz : m * y 0 = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hm)
  · intro he
    rw [he, mul_zero, add_zero]

theorem ProfileEquation.passive_head_eq_iff {y : ℝ → ℝ} (h : ProfileEquation W 1 y)
    (hm : 0 < m) :
    profileIntegralCost W m 1 y = m * (W.primitive 1 - W.moment 1) ↔ y 1 = 0 := by
  rw [h.cost_passive_head]
  constructor
  · intro he
    have hz : m * y 1 = 0 := by linarith
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt hm)
  · intro he
    rw [he, mul_zero, add_zero]

end TimeTraps.Graph
