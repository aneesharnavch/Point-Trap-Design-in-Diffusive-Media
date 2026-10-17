module

public import TimeTraps.Interval.CellContinuity

@[expose] public section

/-!
Comparison of the actual balanced barriers for two continuous positive
source-coordinate media. The cells and trial sites are identical in both
problems. Strict comparison is proved by the weighted integral inequalities,
including cells whose endpoints are 0 or 1.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis

theorem CellWeight.leftRise_mono_weight (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x)
    {α c : ℝ} (hα : 0 ≤ α) (hc : c ≤ 1) (hac : α ≤ c) :
    W.leftRise α c ≤ V.leftRise α c := by
  have hW : ContinuousOn (fun x => W.value x * (x - α)) (Icc α c) :=
    (W.continuous.mul (continuousOn_id.sub continuousOn_const)).mono
    (Icc_subset_Icc hα hc)
  have hV : ContinuousOn (fun x => V.value x * (x - α)) (Icc α c) :=
    (V.continuous.mul (continuousOn_id.sub continuousOn_const)).mono
    (Icc_subset_Icc hα hc)
  exact intervalIntegral.integral_mono_on hac
    (hW.intervalIntegrable_of_Icc hac) (hV.intervalIntegrable_of_Icc hac)
    (fun x hx => mul_le_mul_of_nonneg_right
      (hWV x ⟨hα.trans hx.1, hx.2.trans hc⟩) (sub_nonneg.mpr hx.1))

theorem CellWeight.rightRise_mono_weight (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x)
    {c β : ℝ} (hc : 0 ≤ c) (hβ : β ≤ 1) (hcb : c ≤ β) :
    W.rightRise β c ≤ V.rightRise β c := by
  have hW : ContinuousOn (fun x => W.value x * (β - x)) (Icc c β) :=
    (W.continuous.mul (continuousOn_const.sub continuousOn_id)).mono
    (Icc_subset_Icc hc hβ)
  have hV : ContinuousOn (fun x => V.value x * (β - x)) (Icc c β) :=
    (V.continuous.mul (continuousOn_const.sub continuousOn_id)).mono
    (Icc_subset_Icc hc hβ)
  exact intervalIntegral.integral_mono_on hcb
    (hW.intervalIntegrable_of_Icc hcb) (hV.intervalIntegrable_of_Icc hcb)
    (fun x hx => mul_le_mul_of_nonneg_right
      (hWV x ⟨hc.trans hx.1, hx.2.trans hβ⟩) (sub_nonneg.mpr hx.2))

theorem CellWeight.leftRise_lt_weight (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x < V.value x)
    {α c : ℝ} (hα : 0 ≤ α) (hc : c ≤ 1) (hac : α < c) :
    W.leftRise α c < V.leftRise α c := by
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hac
    ((W.continuous.mul (continuousOn_id.sub continuousOn_const)).mono (Icc_subset_Icc hα hc))
    ((V.continuous.mul (continuousOn_id.sub continuousOn_const)).mono (Icc_subset_Icc hα hc))
  · intro x hx
    exact mul_le_mul_of_nonneg_right
      (hWV x ⟨hα.trans hx.1.le, hx.2.trans hc⟩).le (sub_nonneg.mpr hx.1.le)
  · exact ⟨c, ⟨hac.le, le_rfl⟩,
      mul_lt_mul_of_pos_right (hWV c ⟨hα.trans hac.le, hc⟩) (sub_pos.mpr hac)⟩

theorem CellWeight.rightRise_lt_weight (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x < V.value x)
    {c β : ℝ} (hc : 0 ≤ c) (hβ : β ≤ 1) (hcb : c < β) :
    W.rightRise β c < V.rightRise β c := by
  apply intervalIntegral.integral_lt_integral_of_continuousOn_of_le_of_exists_lt hcb
    ((W.continuous.mul (continuousOn_const.sub continuousOn_id)).mono (Icc_subset_Icc hc hβ))
    ((V.continuous.mul (continuousOn_const.sub continuousOn_id)).mono (Icc_subset_Icc hc hβ))
  · intro x hx
    exact mul_le_mul_of_nonneg_right
      (hWV x ⟨hc.trans hx.1.le, hx.2.trans hβ⟩).le (sub_nonneg.mpr hx.2)
  · exact ⟨c, ⟨le_rfl, hcb.le⟩,
      mul_lt_mul_of_pos_right (hWV c ⟨hc, hcb.le.trans hβ⟩) (sub_pos.mpr hcb)⟩

theorem CellWeight.trialHeight_center_closed (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.trialHeight α β (W.center α β) = W.barrier α β := by
  rcases hab.lt_or_eq with hlt | rfl
  · exact W.trialHeight_center hα hβ hlt
  · simp only [trialHeight, W.center_diagonal, W.barrier_diagonal,
      W.leftRise_self, W.rightRise_self, max_self]

theorem CellWeight.trialHeight_mono_weight (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x)
    {α β c : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (hc : c ∈ Icc α β) :
    W.trialHeight α β c ≤ V.trialHeight α β c :=
  max_le_max (W.leftRise_mono_weight V hWV hα (hc.2.trans hβ) hc.1)
    (W.rightRise_mono_weight V hWV (hα.trans hc.1) hβ hc.2)

theorem CellWeight.barrier_mono_weight (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.barrier α β ≤ V.barrier α β := by
  have hc := V.center_mem hα hβ hab
  calc
    _ ≤ W.trialHeight α β (V.center α β) :=
      (W.local_minimax_closed hα hβ hab).2 ⟨V.center α β, hc, rfl⟩
    _ ≤ V.trialHeight α β (V.center α β) := W.trialHeight_mono_weight V hWV hα hβ hc
    _ = _ := V.trialHeight_center_closed hα hβ hab

theorem CellWeight.barrier_lt_weight (W V : CellWeight)
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x < V.value x)
    {α β : ℝ} (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) :
    W.barrier α β < V.barrier α β := by
  have hc := (V.center_spec hα hβ hab).1
  have hl := W.leftRise_lt_weight V hWV hα (hc.2.le.trans hβ) hc.1
  have hr := W.rightRise_lt_weight V hWV (hα.trans hc.1.le) hβ hc.2
  calc
    _ ≤ W.trialHeight α β (V.center α β) :=
      (W.local_minimax_closed hα hβ hab.le).2 ⟨V.center α β, Ioo_subset_Icc_self hc, rfl⟩
    _ < V.trialHeight α β (V.center α β) := max_lt_max hl hr
    _ = _ := V.trialHeight_center hα hβ hab

end TimeTraps.Interval
