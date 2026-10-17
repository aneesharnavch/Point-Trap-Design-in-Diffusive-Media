module

public import TimeTraps.Interval.BalancedCell
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-!
Exact constant-weight cell formulas. Constancy is required only on the
physical source interval. The midpoint and quadratic barrier follow from
the defining rise integrals and the already proved strict minimax theorem.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis

theorem CellWeight.leftRise_constant (W : CellWeight) {C α c : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C)
    (hα : 0 ≤ α) (hc : c ≤ 1) (hac : α ≤ c) :
    W.leftRise α c = C * (c - α) ^ 2 / 2 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => C * (t - α) ^ 2 / 2) (C * (x - α)) x := by
    have ht := ((((hasDerivAt_id x).sub_const α).pow 2).const_mul C).div_const 2
    have he : C * ((2 : ℝ) * (x - α) ^ (2 - 1) * 1) / 2 = C * (x - α) := by ring
    change HasDerivAt (fun t : ℝ => C * (t - α) ^ 2 / 2)
      (C * ((2 : ℝ) * (x - α) ^ (2 - 1) * 1) / 2) x at ht
    rw [he] at ht
    exact ht
  have hi := integral_derivative_to_point
    ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).div_const 2).continuousOn
    (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
    (fun x _ => hd x) (show c ∈ Icc α c from ⟨hac, le_rfl⟩)
  change (∫ t in α..c, C * (t - α)) = C * (c - α) ^ 2 / 2 - C * (α - α) ^ 2 / 2 at hi
  calc
    W.leftRise α c = ∫ t in α..c, C * (t - α) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hac
      intro t ht
      dsimp only
      rw [hC t ⟨hα.trans ht.1.le, ht.2.le.trans hc⟩]
    _ = _ := by rw [hi]; ring

theorem CellWeight.rightRise_constant (W : CellWeight) {C β c : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C)
    (hc : 0 ≤ c) (hβ : β ≤ 1) (hcb : c ≤ β) :
    W.rightRise β c = C * (β - c) ^ 2 / 2 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => -C * (β - t) ^ 2 / 2) (C * (β - x)) x := by
    have ht := ((((hasDerivAt_id x).const_sub β).pow 2).const_mul (-C)).div_const 2
    have he : -C * ((2 : ℝ) * (β - x) ^ (2 - 1) * (-1)) / 2 = C * (β - x) := by ring
    change HasDerivAt (fun t : ℝ => -C * (β - t) ^ 2 / 2)
      (-C * ((2 : ℝ) * (β - x) ^ (2 - 1) * (-1)) / 2) x at ht
    rw [he] at ht
    exact ht
  have hi := integral_derivative_to_point
    ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).div_const 2).continuousOn
    (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn
    (fun x _ => hd x) (show β ∈ Icc c β from ⟨hcb, le_rfl⟩)
  change (∫ t in c..β, C * (β - t)) = -C * (β - β) ^ 2 / 2 - (-C * (β - c) ^ 2 / 2) at hi
  calc
    W.rightRise β c = ∫ t in c..β, C * (β - t) := by
      apply intervalIntegral.integral_congr_Ioo_of_le hcb
      intro t ht
      dsimp only
      rw [hC t ⟨hc.trans ht.1.le, ht.2.le.trans hβ⟩]
    _ = _ := by rw [hi]; ring

theorem CellWeight.center_constant (W : CellWeight) {C α β : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) : W.center α β = (α + β) / 2 := by
  rcases hab.lt_or_eq with hlt | rfl
  · have hc : (α + β) / 2 ∈ Icc α β := by constructor <;> linarith
    apply W.center_eq_of_balanced hα hβ hlt hc
    rw [W.leftRise_constant hC hα (hc.2.trans hβ) hc.1,
      W.rightRise_constant hC (hα.trans hc.1) hβ hc.2]
    ring
  · rw [W.center_diagonal]
    ring

theorem CellWeight.barrier_constant (W : CellWeight) {C α β : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.barrier α β = C * (β - α) ^ 2 / 8 := by
  have hc : (α + β) / 2 ∈ Icc α β := by constructor <;> linarith
  rw [CellWeight.barrier, W.center_constant hC hα hβ hab,
    W.leftRise_constant hC hα (hc.2.trans hβ) hc.1]
  ring

theorem CellWeight.constant_minimax_eq_iff (W : CellWeight) {C α β c : ℝ}
    (hC : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = C)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α < β) (hc : c ∈ Icc α β) :
    W.trialHeight α β c = C * (β - α) ^ 2 / 8 ↔ c = (α + β) / 2 := by
  rw [← W.barrier_constant hC hα hβ hab.le, W.trialHeight_eq_iff hα hβ hab hc,
    W.center_constant hC hα hβ hab.le]

end TimeTraps.Interval
