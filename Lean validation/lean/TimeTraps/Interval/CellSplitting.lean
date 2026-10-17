module

public import TimeTraps.Interval.CellContinuity

@[expose] public section

/-!
Strict improvement under an interior cell split. Boundary comparisons come
from exact integral identities and positivity. The strict minimax theorem
then handles the location of the parent center relative to the split point.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis

theorem CellWeight.primitive_strictMono (W : CellWeight) : StrictMonoOn W.primitive (Icc 0 1) :=
  integral_primitive_strictMonoOn zero_le_one W.continuous
    (fun x hx => W.positive x (Ioo_subset_Icc_self hx))

theorem CellWeight.rightRise_endpoint_difference (W : CellWeight) {c γ β : ℝ}
    (hc : c ∈ Icc 0 1) (hγ : γ ∈ Icc 0 1) (hβ : β ∈ Icc 0 1) :
    W.rightRise β c - W.rightRise γ c =
      W.rightRise β γ + (β - γ) * (W.primitive γ - W.primitive c) := by
  rw [W.rightRise_formula hβ hc, W.rightRise_formula hγ hc, W.rightRise_formula hβ hγ]
  ring

theorem CellWeight.leftRise_endpoint_difference (W : CellWeight) {α γ c : ℝ}
    (hα : α ∈ Icc 0 1) (hγ : γ ∈ Icc 0 1) (hc : c ∈ Icc 0 1) :
    W.leftRise α c - W.leftRise γ c =
      W.leftRise α γ + (γ - α) * (W.primitive c - W.primitive γ) := by
  rw [W.leftRise_formula hα hc, W.leftRise_formula hγ hc, W.leftRise_formula hα hγ]
  ring

theorem CellWeight.rightRise_strict_endpoint (W : CellWeight) {c γ β : ℝ}
    (hc : 0 ≤ c) (hβ : β ≤ 1) (hcg : c ≤ γ) (hgb : γ < β) :
    W.rightRise γ c < W.rightRise β c := by
  have hcu : c ∈ Icc (0 : ℝ) 1 := ⟨hc, hcg.trans (hgb.le.trans hβ)⟩
  have hgu : γ ∈ Icc (0 : ℝ) 1 := ⟨hc.trans hcg, hgb.le.trans hβ⟩
  have hbu : β ∈ Icc (0 : ℝ) 1 := ⟨hgu.1.trans hgb.le, hβ⟩
  have hid := W.rightRise_endpoint_difference hcu hgu hbu
  have hp := W.rightRise_pos hgu.1 hβ hgb
  have hn := mul_nonneg (sub_pos.mpr hgb).le
    (sub_nonneg.mpr (W.primitive_strictMono.monotoneOn hcu hgu hcg))
  linarith

theorem CellWeight.leftRise_strict_endpoint (W : CellWeight) {α γ c : ℝ}
    (hα : 0 ≤ α) (hc : c ≤ 1) (hag : α < γ) (hgc : γ ≤ c) :
    W.leftRise γ c < W.leftRise α c := by
  have hau : α ∈ Icc (0 : ℝ) 1 := ⟨hα, hag.le.trans (hgc.trans hc)⟩
  have hgu : γ ∈ Icc (0 : ℝ) 1 := ⟨hα.trans hag.le, hgc.trans hc⟩
  have hcu : c ∈ Icc (0 : ℝ) 1 := ⟨hgu.1.trans hgc, hc⟩
  have hid := W.leftRise_endpoint_difference hau hgu hcu
  have hp := W.leftRise_pos hα hgu.2 hag
  have hn := mul_nonneg (sub_pos.mpr hag).le
    (sub_nonneg.mpr (W.primitive_strictMono.monotoneOn hgu hcu hgc))
  linarith

theorem CellWeight.barrier_split_left (W : CellWeight) {α γ β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hag : α < γ) (hgb : γ < β) :
    W.barrier α γ < W.barrier α β := by
  have hab := hag.trans hgb
  have hs := W.center_spec hα hβ hab
  have ht := W.center_spec hα (hgb.le.trans hβ) hag
  by_cases hg : γ ≤ W.center α β
  · change W.leftRise α (W.center α γ) < W.leftRise α (W.center α β)
    exact W.leftRise_strictMono hα hβ hab.le
      ⟨ht.1.1.le, ht.1.2.le.trans hgb.le⟩ (Ioo_subset_Icc_self hs.1) (ht.1.2.trans_le hg)
  · have hcg : W.center α β < γ := lt_of_not_ge hg
    have hc : W.center α β ∈ Icc α γ := ⟨hs.1.1.le, hcg.le⟩
    have hr := W.rightRise_strict_endpoint (hα.trans hs.1.1.le) hβ hcg.le hgb
    have hn : W.center α β ≠ W.center α γ := by
      intro he
      have hbal := ht.2
      rw [← he] at hbal
      linarith [hs.2]
    have hm : W.trialHeight α γ (W.center α β) = W.barrier α β := by
      unfold CellWeight.trialHeight
      rw [max_eq_left (by linarith [hs.2])]
      rfl
    exact (W.barrier_lt_trial_of_ne hα (hgb.le.trans hβ) hag hc hn).trans_eq hm

theorem CellWeight.barrier_split_right (W : CellWeight) {α γ β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hag : α < γ) (hgb : γ < β) :
    W.barrier γ β < W.barrier α β := by
  have hab := hag.trans hgb
  have hs := W.center_spec hα hβ hab
  have ht := W.center_spec (hα.trans hag.le) hβ hgb
  by_cases hg : W.center α β ≤ γ
  · change W.leftRise γ (W.center γ β) < W.leftRise α (W.center α β)
    rw [ht.2, hs.2]
    exact W.rightRise_strictAnti hα hβ hab.le (Ioo_subset_Icc_self hs.1)
      ⟨hag.le.trans ht.1.1.le, ht.1.2.le⟩ (hg.trans_lt ht.1.1)
  · have hgc : γ < W.center α β := lt_of_not_ge hg
    have hc : W.center α β ∈ Icc γ β := ⟨hgc.le, hs.1.2.le⟩
    have hl := W.leftRise_strict_endpoint hα (hs.1.2.le.trans hβ) hag hgc.le
    have hn : W.center α β ≠ W.center γ β := by
      intro he
      have hbal := ht.2
      rw [← he] at hbal
      linarith [hs.2]
    have hm : W.trialHeight γ β (W.center α β) = W.barrier α β := by
      unfold CellWeight.trialHeight
      rw [max_eq_right (by linarith [hs.2])]
      exact hs.2.symm
    exact (W.barrier_lt_trial_of_ne (hα.trans hag.le) hβ hgb hc hn).trans_eq hm

/-- Both nondegenerate children of an interior split have strictly smaller
barriers than their parent. -/
theorem CellWeight.barrier_split (W : CellWeight) {α γ β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hag : α < γ) (hgb : γ < β) :
    W.barrier α γ < W.barrier α β ∧ W.barrier γ β < W.barrier α β :=
  ⟨W.barrier_split_left hα hβ hag hgb, W.barrier_split_right hα hβ hag hgb⟩

/-- Every nondegenerate proper subcell has strictly smaller barrier, including
subcells obtained by trimming both ends of the parent. -/
theorem CellWeight.barrier_strict_subcell (W : CellWeight) {α γ δ β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hag : α ≤ γ) (hgd : γ < δ) (hdb : δ ≤ β)
    (hproper : α < γ ∨ δ < β) : W.barrier γ δ < W.barrier α β := by
  rcases hproper with hleft | hright
  · have hp := W.barrier_split_right hα hβ hleft (hgd.trans_le hdb)
    rcases hdb.lt_or_eq with hlt | rfl
    · exact (W.barrier_split_left (hα.trans hag) hβ hgd hlt).trans hp
    · exact hp
  · have hp := W.barrier_split_left hα hβ (hag.trans_lt hgd) hright
    rcases hag.lt_or_eq with hlt | rfl
    · exact (W.barrier_split_right hα (hdb.trans hβ) hlt hgd).trans hp
    · exact hp

theorem CellWeight.barrier_subcell_le (W : CellWeight) {α γ δ β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hag : α ≤ γ) (hgd : γ ≤ δ) (hdb : δ ≤ β) :
    W.barrier γ δ ≤ W.barrier α β := by
  rcases hgd.lt_or_eq with hlt | rfl
  · rcases hag.lt_or_eq with hleft | rfl
    · exact (W.barrier_strict_subcell hα hβ hag hlt hdb (Or.inl hleft)).le
    · rcases hdb.lt_or_eq with hright | rfl
      · exact (W.barrier_strict_subcell hα hβ le_rfl hlt hdb (Or.inr hright)).le
      · exact le_refl _
  · rw [W.barrier_diagonal]
    exact W.barrier_nonneg hα hβ (hag.trans hdb)

end TimeTraps.Interval
