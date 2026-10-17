module

public import TimeTraps.Interval.CellSplitting

@[expose] public section

/-!
The geometric height comparison, including trial sites outside their cell.
Its two rise comparisons will be derived from the actual absorption CDF.
The conclusion includes the necessary balancing and boundary-height equality.
-/

namespace TimeTraps.Interval

open Set

theorem CellWeight.barrier_lt_left_full (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) : W.barrier α β < W.leftRise α β := by
  have hc := W.center_spec hα hβ hab
  exact W.leftRise_strictMono hα hβ hab.le (Ioo_subset_Icc_self hc.1) ⟨hab.le, le_rfl⟩ hc.1.2

theorem CellWeight.barrier_lt_right_full (W : CellWeight) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) : W.barrier α β < W.rightRise β α := by
  have hc := W.center_spec hα hβ hab
  rw [CellWeight.barrier, hc.2]
  exact W.rightRise_strictAnti hα hβ hab.le ⟨le_rfl, hab.le⟩ (Ioo_subset_Icc_self hc.1) hc.1.1

/-- The two integrated comparisons force the height barrier for every trial
site in [0,1], without assuming that the site lies in its assigned cell. -/
theorem CellWeight.height_comparison (W : CellWeight) {α β c M va vb vc : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) (hc : c ∈ Icc 0 1)
    (haM : va ≤ M) (hbM : vb ≤ M)
    (hleft : α ≤ c → W.leftRise α c ≤ va - vc)
    (hright : c ≤ β → W.rightRise β c ≤ vb - vc) :
    W.barrier α β ≤ M - vc ∧
      (M - vc = W.barrier α β → c = W.center α β ∧ va = M ∧ vb = M) := by
  by_cases hca : c < α
  · have hr := W.rightRise_strictAnti hc.1 hβ (hca.trans hab).le
      ⟨le_rfl, (hca.trans hab).le⟩ ⟨hca.le, hab.le⟩ hca
    have hb := W.barrier_lt_right_full hα hβ hab
    have hh := hright (hca.trans hab).le
    have hstrict : W.barrier α β < M - vc := by linarith
    exact ⟨hstrict.le, fun he => False.elim (by linarith)⟩
  by_cases hbc : β < c
  · have hl := W.leftRise_strictMono hα hc.2 (hab.trans hbc).le
      ⟨hab.le, hbc.le⟩ ⟨(hab.trans hbc).le, le_rfl⟩ hbc
    have hb := W.barrier_lt_left_full hα hβ hab
    have hh := hleft (hab.trans hbc).le
    have hstrict : W.barrier α β < M - vc := by linarith
    exact ⟨hstrict.le, fun he => False.elim (by linarith)⟩
  have hcell : c ∈ Icc α β := ⟨le_of_not_gt hca, le_of_not_gt hbc⟩
  have hl := hleft hcell.1
  have hr := hright hcell.2
  have htrial : W.trialHeight α β c ≤ M - vc :=
    max_le (by linarith) (by linarith)
  have hbarrier : W.barrier α β ≤ W.trialHeight α β c :=
    (W.local_minimax hα hβ hab).2 ⟨c, hcell, rfl⟩
  refine ⟨hbarrier.trans htrial, ?_⟩
  intro he
  have hte : W.trialHeight α β c = W.barrier α β := by linarith
  have hcenter := (W.trialHeight_eq_iff hα hβ hab hcell).mp hte
  have hL : W.leftRise α c = W.barrier α β := by rw [hcenter]; rfl
  have hR : W.rightRise β c = W.barrier α β := by
    rw [hcenter, ← (W.center_spec hα hβ hab).2]
    rfl
  exact ⟨hcenter, by linarith, by linarith⟩

end TimeTraps.Interval
