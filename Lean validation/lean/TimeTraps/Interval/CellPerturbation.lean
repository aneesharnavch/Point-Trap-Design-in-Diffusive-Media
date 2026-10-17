module

public import TimeTraps.Interval.CellComparison
public import Mathlib.Analysis.Calculus.Deriv.Pow

@[expose] public section

/-!
Certified perturbation of the defining rise integrals and their balanced
minimax barrier. All estimates compare the same source-coordinate cell.
The constant is obtained by exact integration of the linear kernels.
-/

namespace TimeTraps.Interval

open Set MeasureTheory TimeTraps.Analysis

theorem integral_left_linear (C α c : ℝ) (hac : α ≤ c) :
    (∫ x in α..c, C * (x - α)) = C * (c - α) ^ 2 / 2 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => C * (t - α) ^ 2 / 2) (C * (x - α)) x := by
    have ht := ((((hasDerivAt_id x).sub_const α).pow 2).const_mul C).div_const 2
    have he : C * ((2 : ℝ) * (x - α) ^ (2 - 1) * 1) / 2 = C * (x - α) := by ring
    change HasDerivAt (fun t : ℝ => C * (t - α) ^ 2 / 2)
      (C * ((2 : ℝ) * (x - α) ^ (2 - 1) * 1) / 2) x at ht
    rwa [he] at ht
  have hi := integral_derivative_to_point
    ((continuous_const.mul ((continuous_id.sub continuous_const).pow 2)).div_const 2).continuousOn
    (continuous_const.mul (continuous_id.sub continuous_const)).continuousOn
    (fun x _ => hd x) (show c ∈ Icc α c from ⟨hac, le_rfl⟩)
  simpa using hi

theorem integral_right_linear (C β c : ℝ) (hcb : c ≤ β) :
    (∫ x in c..β, C * (β - x)) = C * (β - c) ^ 2 / 2 := by
  have hd (x : ℝ) : HasDerivAt (fun t : ℝ => -C * (β - t) ^ 2 / 2) (C * (β - x)) x := by
    have ht := ((((hasDerivAt_id x).const_sub β).pow 2).const_mul (-C)).div_const 2
    have he : -C * ((2 : ℝ) * (β - x) ^ (2 - 1) * (-1)) / 2 = C * (β - x) := by ring
    change HasDerivAt (fun t : ℝ => -C * (β - t) ^ 2 / 2)
      (-C * ((2 : ℝ) * (β - x) ^ (2 - 1) * (-1)) / 2) x at ht
    rwa [he] at ht
  have hi := integral_derivative_to_point
    ((continuous_const.mul ((continuous_const.sub continuous_id).pow 2)).div_const 2).continuousOn
    (continuous_const.mul (continuous_const.sub continuous_id)).continuousOn
    (fun x _ => hd x) (show β ∈ Icc c β from ⟨hcb, le_rfl⟩)
  calc
    _ = -C * (β - β) ^ 2 / 2 - (-C * (β - c) ^ 2 / 2) := hi
    _ = _ := by ring

theorem CellWeight.leftRise_le_add_weight (W V : CellWeight) {ε α c : ℝ}
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x + ε)
    (hα : 0 ≤ α) (hc : c ≤ 1) (hac : α ≤ c) :
    W.leftRise α c ≤ V.leftRise α c + ε * (c - α) ^ 2 / 2 := by
  have hW : ContinuousOn (fun x => W.value x * (x - α)) (Icc α c) :=
    (W.continuous.mul (continuousOn_id.sub continuousOn_const)).mono
    (Icc_subset_Icc hα hc)
  have hV : ContinuousOn (fun x => V.value x * (x - α)) (Icc α c) :=
    (V.continuous.mul (continuousOn_id.sub continuousOn_const)).mono
    (Icc_subset_Icc hα hc)
  have hε : IntervalIntegrable (fun x => ε * (x - α)) volume α c :=
    (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable α c
  calc
    _ ≤ ∫ x in α..c, V.value x * (x - α) + ε * (x - α) := by
      apply intervalIntegral.integral_mono_on hac
        (hW.intervalIntegrable_of_Icc hac) ((hV.intervalIntegrable_of_Icc hac).add hε)
      intro x hx
      have h := mul_le_mul_of_nonneg_right (hWV x ⟨hα.trans hx.1, hx.2.trans hc⟩)
        (sub_nonneg.mpr hx.1)
      nlinarith only [h]
    _ = _ := by rw [intervalIntegral.integral_add (hV.intervalIntegrable_of_Icc hac) hε,
      integral_left_linear ε α c hac]; rfl

theorem CellWeight.rightRise_le_add_weight (W V : CellWeight) {ε c β : ℝ}
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x + ε)
    (hc : 0 ≤ c) (hβ : β ≤ 1) (hcb : c ≤ β) :
    W.rightRise β c ≤ V.rightRise β c + ε * (β - c) ^ 2 / 2 := by
  have hW : ContinuousOn (fun x => W.value x * (β - x)) (Icc c β) :=
    (W.continuous.mul (continuousOn_const.sub continuousOn_id)).mono
    (Icc_subset_Icc hc hβ)
  have hV : ContinuousOn (fun x => V.value x * (β - x)) (Icc c β) :=
    (V.continuous.mul (continuousOn_const.sub continuousOn_id)).mono
    (Icc_subset_Icc hc hβ)
  have hε : IntervalIntegrable (fun x => ε * (β - x)) volume c β :=
    (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable c β
  calc
    _ ≤ ∫ x in c..β, V.value x * (β - x) + ε * (β - x) := by
      apply intervalIntegral.integral_mono_on hcb
        (hW.intervalIntegrable_of_Icc hcb) ((hV.intervalIntegrable_of_Icc hcb).add hε)
      intro x hx
      have h := mul_le_mul_of_nonneg_right (hWV x ⟨hc.trans hx.1, hx.2.trans hβ⟩)
        (sub_nonneg.mpr hx.2)
      nlinarith only [h]
    _ = _ := by rw [intervalIntegral.integral_add (hV.intervalIntegrable_of_Icc hcb) hε,
      integral_right_linear ε β c hcb]; rfl

theorem CellWeight.leftRise_abs_sub_le (W V : CellWeight) {ε α c : ℝ}
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε)
    (hα : 0 ≤ α) (hc : c ≤ 1) (hac : α ≤ c) :
    |W.leftRise α c - V.leftRise α c| ≤ ε * (c - α) ^ 2 / 2 := by
  have hl := W.leftRise_le_add_weight V (ε := ε)
    (fun x hx => by linarith [(abs_le.mp (hWV x hx)).2]) hα hc hac
  have hr := V.leftRise_le_add_weight W (ε := ε)
    (fun x hx => by linarith [(abs_le.mp (hWV x hx)).1]) hα hc hac
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem CellWeight.rightRise_abs_sub_le (W V : CellWeight) {ε c β : ℝ}
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε)
    (hc : 0 ≤ c) (hβ : β ≤ 1) (hcb : c ≤ β) :
    |W.rightRise β c - V.rightRise β c| ≤ ε * (β - c) ^ 2 / 2 := by
  have hl := W.rightRise_le_add_weight V (ε := ε)
    (fun x hx => by linarith [(abs_le.mp (hWV x hx)).2]) hc hβ hcb
  have hr := V.rightRise_le_add_weight W (ε := ε)
    (fun x hx => by linarith [(abs_le.mp (hWV x hx)).1]) hc hβ hcb
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem CellWeight.trialHeight_le_add_weight (W V : CellWeight) {ε α β c : ℝ}
    (hε : 0 ≤ ε) (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x + ε)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hc : c ∈ Icc α β) :
    W.trialHeight α β c ≤ V.trialHeight α β c + ε * (β - α) ^ 2 / 2 := by
  have hl := W.leftRise_le_add_weight V hWV hα (hc.2.trans hβ) hc.1
  have hr := W.rightRise_le_add_weight V hWV (hα.trans hc.1) hβ hc.2
  have hl2 : (c - α) ^ 2 ≤ (β - α) ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hc.1) (sub_nonneg.mpr (hc.1.trans hc.2))).mpr (by linarith [hc.2])
  have hr2 : (β - c) ^ 2 ≤ (β - α) ^ 2 :=
    (sq_le_sq₀ (sub_nonneg.mpr hc.2) (sub_nonneg.mpr (hc.1.trans hc.2))).mpr (by linarith [hc.1])
  have hlε := mul_le_mul_of_nonneg_left hl2 hε
  have hrε := mul_le_mul_of_nonneg_left hr2 hε
  apply max_le
  · have hm : V.leftRise α c ≤ V.trialHeight α β c := le_max_left _ _
    linarith
  · have hm : V.rightRise β c ≤ V.trialHeight α β c := le_max_right _ _
    linarith

theorem CellWeight.barrier_le_add_weight (W V : CellWeight) {ε α β : ℝ}
    (hε : 0 ≤ ε) (hWV : ∀ x ∈ Icc (0 : ℝ) 1, W.value x ≤ V.value x + ε)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    W.barrier α β ≤ V.barrier α β + ε * (β - α) ^ 2 / 2 := by
  have hc := V.center_mem hα hβ hab
  calc
    _ ≤ W.trialHeight α β (V.center α β) :=
      (W.local_minimax_closed hα hβ hab).2 ⟨V.center α β, hc, rfl⟩
    _ ≤ V.trialHeight α β (V.center α β) + ε * (β - α) ^ 2 / 2 :=
      W.trialHeight_le_add_weight V hε hWV hα hβ hc
    _ = _ := by rw [V.trialHeight_center_closed hα hβ hab]

theorem CellWeight.barrier_abs_sub_le (W V : CellWeight) {ε α β : ℝ}
    (hWV : ∀ x ∈ Icc (0 : ℝ) 1, |W.value x - V.value x| ≤ ε)
    (hα : 0 ≤ α) (hβ : β ≤ 1) (hab : α ≤ β) :
    |W.barrier α β - V.barrier α β| ≤ ε * (β - α) ^ 2 / 2 := by
  have hε : 0 ≤ ε := (abs_nonneg _).trans (hWV 0 ⟨le_rfl, zero_le_one⟩)
  have hl := W.barrier_le_add_weight V hε
    (fun x hx => by linarith [(abs_le.mp (hWV x hx)).2]) hα hβ hab
  have hr := V.barrier_le_add_weight W hε
    (fun x hx => by linarith [(abs_le.mp (hWV x hx)).1]) hα hβ hab
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end TimeTraps.Interval
