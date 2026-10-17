module

public import TimeTraps.Interval.EndpointCell

@[expose] public section

/-! Reflection of symmetric source-coordinate weights exchanges the two
one-sided barriers and preserves the ordinary balanced-cell barrier. -/

namespace TimeTraps.Interval

open Set MeasureTheory

variable (W : CellWeight)
  (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value (1 - z) = W.value z)

include hW

theorem CellWeight.leftRise_reflect {β c : ℝ}
    (hβ : β ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) :
    W.leftRise (1 - β) (1 - c) = W.rightRise β c := by
  unfold leftRise rightRise
  calc
    _ = ∫ z in (1 - β)..(1 - c), W.value (1 - z) * (β - (1 - z)) := by
      apply intervalIntegral.integral_congr
      intro z hz
      have hm : z ∈ Icc (0 : ℝ) 1 := by
        have h₁ : (0 : ℝ) ≤ min (1 - β) (1 - c) := le_min (by linarith [hβ.2]) (by linarith [hc.2])
        have h₂ : max (1 - β) (1 - c) ≤ (1 : ℝ) := max_le (by linarith [hβ.1]) (by linarith [hc.1])
        exact ⟨h₁.trans hz.1, hz.2.trans h₂⟩
      dsimp only
      rw [hW z hm]
      ring
    _ = _ := by
      simpa only [sub_sub_cancel] using
        (intervalIntegral.integral_comp_sub_left (fun z => W.value z * (β - z))
          (a := 1 - β) (b := 1 - c) 1)

theorem CellWeight.rightRise_reflect {α c : ℝ}
    (hα : α ∈ Icc (0 : ℝ) 1) (hc : c ∈ Icc (0 : ℝ) 1) :
    W.rightRise (1 - α) (1 - c) = W.leftRise α c := by
  have ha : 1 - α ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hα.2], by linarith [hα.1]⟩
  have hd : 1 - c ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc.2], by linarith [hc.1]⟩
  simpa only [sub_sub_cancel] using (W.leftRise_reflect hW ha hd).symm

theorem CellWeight.center_reflect {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.center (1 - β) (1 - α) = 1 - W.center α β := by
  rcases hab.lt_or_eq with hlt | rfl
  · obtain ⟨hc, he⟩ := W.center_spec hα hβ hlt
    have hcm : W.center α β ∈ Icc (0 : ℝ) 1 := ⟨by linarith [hc.1], by linarith [hc.2]⟩
    apply W.center_eq_of_balanced (by linarith) (by linarith) (by linarith)
      ⟨by linarith [hc.2], by linarith [hc.1]⟩
    rw [W.leftRise_reflect hW ⟨hα.trans hlt.le, hβ⟩ hcm,
      W.rightRise_reflect hW ⟨hα, hlt.le.trans hβ⟩ hcm]
    exact he.symm
  · rw [W.center_diagonal, W.center_diagonal]

theorem CellWeight.barrier_reflect {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.barrier (1 - β) (1 - α) = W.barrier α β := by
  rw [barrier, W.center_reflect hW hα hβ hab]
  have hc := W.center_mem hα hβ hab
  rw [W.leftRise_reflect hW ⟨hα.trans hab, hβ⟩ ⟨hα.trans hc.1, hc.2.trans hβ⟩]
  exact (W.orientedBarrier_ordinary_right_integral hα hβ hab).symm

def CellKind.reflect : CellKind → CellKind
  | .ordinary => .ordinary
  | .leftEndpoint => .rightEndpoint
  | .rightEndpoint => .leftEndpoint

theorem CellWeight.orientedBarrier_reflect (kind : CellKind) {α β : ℝ}
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.orientedBarrier kind.reflect (1 - β) (1 - α) = W.orientedBarrier kind α β := by
  cases kind with
  | ordinary => exact W.barrier_reflect hW hα hβ hab
  | leftEndpoint => exact W.leftRise_reflect hW ⟨hα.trans hab, hβ⟩ ⟨hα, hab.trans hβ⟩
  | rightEndpoint => exact W.rightRise_reflect hW ⟨hα, hab.trans hβ⟩ ⟨hα.trans hab, hβ⟩

end TimeTraps.Interval
