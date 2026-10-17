module

public import TimeTraps.Graph.ProfileMoment

@[expose] public section

/-! Exact integration identities for the source-coordinate deficit profile.
The derivative is required only in the open interval; no differentiability
of the positive continuous weight is assumed. -/

namespace TimeTraps.Graph

open Set MeasureTheory TimeTraps.Analysis TimeTraps.Interval

structure ProfileEquation (W : CellWeight) (α : ℝ) (y : ℝ → ℝ) : Prop where
  continuous : ContinuousOn y (Icc 0 1)
  derivative : ∀ z ∈ Ioo 0 1, HasDerivAt y (W.value z * (z - α)) z

noncomputable def profileIntegralCost (W : CellWeight) (m α : ℝ) (y : ℝ → ℝ) : ℝ :=
  m * ∫ z in (0 : ℝ)..1, y z + W.value z * (z - α) ^ 2

variable {W : CellWeight} {α : ℝ} {y : ℝ → ℝ}

theorem ProfileEquation.integrable (h : ProfileEquation W α y) :
    IntervalIntegrable (fun z => y z + W.value z * (z - α) ^ 2) volume 0 1 := by
  have hc : ContinuousOn (fun z => y z + W.value z * (z - α) ^ 2) (Icc 0 1) :=
    h.continuous.add (W.continuous.mul ((continuousOn_id.sub continuousOn_const).pow 2))
  exact hc.intervalIntegrable_of_Icc zero_le_one

theorem ProfileEquation.cost_boundary (h : ProfileEquation W α y) (m : ℝ) :
    profileIntegralCost W m α y = m * ((1 - α) * y 1 + α * y 0) := by
  have hd (z : ℝ) (hz : z ∈ Ioo 0 1) :
      HasDerivAt (fun t => (t - α) * y t) (y z + W.value z * (z - α) ^ 2) z := by
    have ht := ((hasDerivAt_id' z).sub_const α).mul (h.derivative z hz)
    convert ht using 1 <;> first | rfl | ring
  have hi := integral_derivative_to_point
    ((continuousOn_id.sub continuousOn_const).mul h.continuous)
    (h.continuous.add (W.continuous.mul ((continuousOn_id.sub continuousOn_const).pow 2)))
    hd (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)
  change (∫ z in (0 : ℝ)..1, y z + W.value z * (z - α) ^ 2) =
    (1 - α) * y 1 - (0 - α) * y 0 at hi
  rw [profileIntegralCost, hi]
  ring

theorem ProfileEquation.value_formula (h : ProfileEquation W α y) {z : ℝ}
    (hz : z ∈ Icc 0 1) : y z = y 0 + W.moment z - α * W.primitive z := by
  have hi := integral_derivative_to_point h.continuous
    (W.continuous.mul (continuousOn_id.sub continuousOn_const)) h.derivative hz
  change (∫ t in (0 : ℝ)..z, W.value t * (t - α)) = y z - y 0 at hi
  have hc := W.continuous.mono (show Icc 0 z ⊆ Icc (0 : ℝ) 1 from
    fun t ht => ⟨ht.1, ht.2.trans hz.2⟩)
  have him : IntervalIntegrable (fun t => W.value t * t) volume 0 z :=
    (hc.mul continuousOn_id).intervalIntegrable_of_Icc hz.1
  have hip : IntervalIntegrable (fun t => α * W.value t) volume 0 z :=
    (continuousOn_const.mul hc).intervalIntegrable_of_Icc hz.1
  have he : (∫ t in (0 : ℝ)..z, W.value t * (t - α)) = W.moment z - α * W.primitive z := by
    calc
      _ = ∫ t in (0 : ℝ)..z, W.value t * t - α * W.value t := by
        apply intervalIntegral.integral_congr
        intro t _
        ring
      _ = _ := by rw [intervalIntegral.integral_sub him hip, intervalIntegral.integral_const_mul]; rfl
  rw [he] at hi
  linarith

theorem ProfileEquation.endpoint_difference (h : ProfileEquation W α y) :
    y 1 - y 0 = W.moment 1 - α * W.primitive 1 := by
  linarith [h.value_formula (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)]

theorem ProfileEquation.cost_interior (h : ProfileEquation W α y) (m : ℝ)
    (hα : α ∈ Icc 0 1) :
    profileIntegralCost W m α y = m * y α + profileCost W m α := by
  rw [h.cost_boundary, profileCost_formula W m hα, h.value_formula hα,
    h.value_formula (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)]
  ring

theorem ProfileEquation.cost_left_difference (h : ProfileEquation W α y) (m : ℝ) :
    profileIntegralCost W m α y - profileCost W m 0 =
      m * (y 0 - α * (W.moment 1 + W.primitive 1 - α * W.primitive 1)) := by
  rw [h.cost_boundary, profileCost_zero,
    h.value_formula (show (1 : ℝ) ∈ Icc 0 1 from ⟨zero_le_one, le_rfl⟩)]
  ring

theorem ProfileEquation.cost_right_difference (h : ProfileEquation W α y) (m : ℝ) :
    profileIntegralCost W m α y - profileCost W m 1 =
      m * (y 1 + (α - 1) * ((α + 1) * W.primitive 1 - W.moment 1)) := by
  have he := h.endpoint_difference
  rw [h.cost_boundary, profileCost_one]
  linear_combination -m * α * he

theorem ProfileEquation.cost_passive_tail {y : ℝ → ℝ} (h : ProfileEquation W 0 y) (m : ℝ) :
    profileIntegralCost W m 0 y = m * W.moment 1 + m * y 0 := by
  rw [h.cost_interior m ⟨le_rfl, zero_le_one⟩, profileCost_zero]
  ring

theorem ProfileEquation.cost_passive_head {y : ℝ → ℝ} (h : ProfileEquation W 1 y) (m : ℝ) :
    profileIntegralCost W m 1 y = m * (W.primitive 1 - W.moment 1) + m * y 1 := by
  rw [h.cost_interior m ⟨zero_le_one, le_rfl⟩, profileCost_one]
  ring

end TimeTraps.Graph
