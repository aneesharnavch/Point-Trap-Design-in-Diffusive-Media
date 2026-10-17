module

public import TimeTraps.Interval.CellRises

@[expose] public section

/-!
Existence, uniqueness, and strict minimax for a balanced source-coordinate
cell. The trial objective is the maximum of the two independent rise
integrals. An explicit primitive-coordinate formula defines the center and
also makes its later dependence on the two endpoints accessible.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis
open scoped Classical

noncomputable def CellWeight.trialHeight (W : CellWeight) (α β c : ℝ) : ℝ :=
  max (W.leftRise α c) (W.rightRise β c)

theorem CellWeight.balanced_existsUnique (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) :
    ∃! c, c ∈ Ioo α β ∧ W.leftRise α c = W.rightRise β c := by
  have hcont := (W.leftRise_continuous hα hβ hab.le).sub (W.rightRise_continuous hα hβ hab.le)
  have hlo : W.leftRise α α - W.rightRise β α < 0 := by
    rw [W.leftRise_self]
    linarith [W.rightRise_pos hα hβ hab]
  have hhi : 0 < W.leftRise α β - W.rightRise β β := by
    rw [W.rightRise_self]
    linarith [W.leftRise_pos hα hβ hab]
  obtain ⟨c, hc, he⟩ := intermediate_value_Icc hab.le hcont ⟨hlo.le, hhi.le⟩
  change W.leftRise α c - W.rightRise β c = 0 at he
  have hca : c ≠ α := by
    intro h
    rw [h] at he
    linarith
  have hcb : c ≠ β := by
    intro h
    rw [h] at he
    linarith
  have hci : c ∈ Ioo α β := ⟨lt_of_le_of_ne hc.1 hca.symm, lt_of_le_of_ne hc.2 hcb⟩
  refine ⟨c, ⟨hci, sub_eq_zero.mp he⟩, ?_⟩
  intro d hd
  apply (W.rise_difference_strictMono hα hβ hab.le).injOn (Ioo_subset_Icc_self hd.1) hc
  dsimp only
  rw [hd.2, sub_self, he]

noncomputable def CellWeight.balanceTarget (W : CellWeight) (α β : ℝ) : ℝ :=
  (W.moment α - α * W.primitive α + β * W.primitive β - W.moment β) / (β - α)

theorem CellWeight.balanced_iff_primitive (W : CellWeight) {α β c : ℝ}
    (hα : α ∈ Icc 0 1) (hβ : β ∈ Icc 0 1) (hc : c ∈ Icc 0 1) (hab : α < β) :
    W.leftRise α c = W.rightRise β c ↔ W.primitive c = W.balanceTarget α β := by
  rw [W.leftRise_formula hα hc, W.rightRise_formula hβ hc]
  unfold CellWeight.balanceTarget
  rw [eq_div_iff (ne_of_gt (sub_pos.mpr hab))]
  constructor <;> intro h <;> nlinarith only [h]

noncomputable def CellWeight.center (W : CellWeight) (α β : ℝ) : ℝ :=
  if α < β then W.sourceInterval.inverse (W.balanceTarget α β / W.sourceInterval.mass) else α

noncomputable def CellWeight.barrier (W : CellWeight) (α β : ℝ) : ℝ :=
  W.leftRise α (W.center α β)

theorem CellWeight.center_diagonal (W : CellWeight) (α : ℝ) : W.center α α = α := by
  simp [CellWeight.center]

theorem CellWeight.barrier_diagonal (W : CellWeight) (α : ℝ) : W.barrier α α = 0 := by
  rw [CellWeight.barrier, W.center_diagonal, W.leftRise_self]

theorem CellWeight.center_eq_of_balanced (W : CellWeight) {α β c : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) (hc : c ∈ Icc α β)
    (hbal : W.leftRise α c = W.rightRise β c) : W.center α β = c := by
  have hcu : c ∈ Icc (0 : ℝ) 1 := ⟨hα.trans hc.1, hc.2.trans hβ⟩
  have he := (W.balanced_iff_primitive ⟨hα, hab.le.trans hβ⟩ ⟨hα.trans hab.le, hβ⟩ hcu hab).mp hbal
  have hcoord : W.sourceInterval.coordinate c = W.balanceTarget α β / W.sourceInterval.mass := by
    change W.primitive c / W.sourceInterval.mass = _
    rw [he]
  unfold CellWeight.center
  rw [if_pos hab, ← hcoord]
  exact W.sourceInterval.inverse_coordinate hcu

theorem CellWeight.center_spec (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) :
    W.center α β ∈ Ioo α β ∧ W.leftRise α (W.center α β) = W.rightRise β (W.center α β) := by
  obtain ⟨c, hc, _⟩ := W.balanced_existsUnique hα hβ hab
  rw [W.center_eq_of_balanced hα hβ hab (Ioo_subset_Icc_self hc.1) hc.2]
  exact hc

theorem CellWeight.center_mem (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) : W.center α β ∈ Icc α β := by
  rcases hab.lt_or_eq with hlt | rfl
  · exact Ioo_subset_Icc_self (W.center_spec hα hβ hlt).1
  · rw [W.center_diagonal]
    exact ⟨le_rfl, le_rfl⟩

theorem CellWeight.balanced_iff_center (W : CellWeight) {α β c : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) (hc : c ∈ Icc α β) :
    W.leftRise α c = W.rightRise β c ↔ c = W.center α β := by
  constructor
  · intro he
    exact (W.center_eq_of_balanced hα hβ hab hc he).symm
  · rintro rfl
    exact (W.center_spec hα hβ hab).2

theorem CellWeight.barrier_pos (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) : 0 < W.barrier α β := by
  have hc := (W.center_spec hα hβ hab).1
  exact W.leftRise_pos hα (hc.2.le.trans hβ) hc.1

theorem CellWeight.barrier_nonneg (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) : 0 ≤ W.barrier α β := by
  rcases hab.lt_or_eq with hlt | rfl
  · exact (W.barrier_pos hα hβ hlt).le
  · rw [W.barrier_diagonal]

theorem CellWeight.trialHeight_center (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) :
    W.trialHeight α β (W.center α β) = W.barrier α β := by
  unfold CellWeight.trialHeight CellWeight.barrier
  rw [← (W.center_spec hα hβ hab).2, max_self]

/-- Every other site, including a cell endpoint, has a strictly larger
maximum rise. -/
theorem CellWeight.barrier_lt_trial_of_ne (W : CellWeight) {α β c : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) (hc : c ∈ Icc α β)
    (hne : c ≠ W.center α β) : W.barrier α β < W.trialHeight α β c := by
  have hs := W.center_spec hα hβ hab
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hr := W.rightRise_strictAnti hα hβ hab.le hc (Ioo_subset_Icc_self hs.1) hlt
    rw [CellWeight.barrier, hs.2]
    exact hr.trans_le (le_max_right _ _)
  · exact (W.leftRise_strictMono hα hβ hab.le (Ioo_subset_Icc_self hs.1) hc hgt).trans_le
      (le_max_left _ _)

theorem CellWeight.local_minimax (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) :
    IsLeast (W.trialHeight α β '' Icc α β) (W.barrier α β) := by
  refine ⟨⟨W.center α β, W.center_mem hα hβ hab.le, W.trialHeight_center hα hβ hab⟩, ?_⟩
  rintro M ⟨c, hc, rfl⟩
  by_cases he : c = W.center α β
  · rw [he, W.trialHeight_center hα hβ hab]
  · exact (W.barrier_lt_trial_of_ne hα hβ hab hc he).le

theorem CellWeight.trialHeight_eq_iff (W : CellWeight) {α β c : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) (hc : c ∈ Icc α β) :
    W.trialHeight α β c = W.barrier α β ↔ c = W.center α β := by
  constructor
  · intro he
    by_contra hn
    have hlt := W.barrier_lt_trial_of_ne hα hβ hab hc hn
    linarith
  · rintro rfl
    exact W.trialHeight_center hα hβ hab

end TimeTraps.Interval
