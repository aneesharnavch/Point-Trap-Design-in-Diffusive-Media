module

public import TimeTraps.Interval.WeightedGridIFTTaylorDesign

@[expose] public section

/-! Signed perturbation integrals and a variational envelope bound for the
actual nearest-node objective. No derivatives of its minimum are assumed. -/

namespace TimeTraps.Interval

open Set MeasureTheory
open scoped Topology ContDiff

variable {n : ℕ}

noncomputable def ClosedPartition.gridSignedCost (Q : ClosedPartition n) (h : ℝ → ℝ) : ℝ :=
  ∫ z in (0 : ℝ)..1, h z * gridDistance Q.point z ^ 2

theorem ClosedPartition.gridSignedCost_integrable (Q : ClosedPartition n) (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (0 : ℝ) 1)) :
    IntervalIntegrable (fun z => h z * gridDistance Q.point z ^ 2) volume 0 1 := by
  apply ContinuousOn.intervalIntegrable_of_Icc zero_le_one
  exact hh.mul ((gridDistance_continuous Q.point).continuousOn.pow 2)

theorem ClosedPartition.gridSignedCost_perturbation (Q R : ClosedPartition n) (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (0 : ℝ) 1)) {H δ : ℝ}
    (hH : ∀ z ∈ Icc (0 : ℝ) 1, |h z| ≤ H)
    (hp : ∀ v, |Q.point v - R.point v| ≤ δ) :
    |Q.gridSignedCost h - R.gridSignedCost h| ≤ 2 * H * δ := by
  have hδ : 0 ≤ δ := (abs_nonneg _).trans (hp 0)
  have hb := intervalIntegral.norm_integral_le_of_norm_le (f := fun z =>
      h z * gridDistance Q.point z ^ 2 - h z * gridDistance R.point z ^ 2)
    zero_le_one (Filter.Eventually.of_forall (fun z hz => ?_))
    (show IntervalIntegrable (fun _ : ℝ => 2 * H * δ) volume 0 1 from intervalIntegrable_const)
  · rw [intervalIntegral.integral_sub (Q.gridSignedCost_integrable h hh)
      (R.gridSignedCost_integrable h hh), Real.norm_eq_abs] at hb
    simpa only [gridSignedCost, intervalIntegral.integral_const, sub_zero, one_smul] using hb
  · have hz' : z ∈ Icc (0 : ℝ) 1 := ⟨hz.1.le, hz.2⟩
    rw [← mul_sub, Real.norm_eq_abs, abs_mul]
    calc
      _ ≤ |h z| * (2 * δ) := mul_le_mul_of_nonneg_left
        (Q.gridDistance_square_lipschitz R hp hz') (abs_nonneg _)
      _ ≤ H * (2 * δ) := mul_le_mul_of_nonneg_right (hH z hz') (by positivity)
      _ = _ := by ring

theorem gridIFT_value_variational_bound (Q R : ClosedPartition n) (W V : CellWeight)
    (h : ℝ → ℝ) (Ω ε : ℝ) (hΩ : 0 < Ω)
    (hV : ∀ z ∈ Icc (0 : ℝ) 1, V.value z = Ω)
    (hW : ∀ z ∈ Icc (0 : ℝ) 1, W.value z = Ω * (1 + ε * h z))
    (hQ : ∀ P : ClosedPartition n, Q.gridCost W ≤ P.gridCost W)
    (hR : ∀ P : ClosedPartition n, R.gridCost V ≤ P.gridCost V) :
    |Q.gridCost W - R.gridCost V - ε * Ω * R.gridSignedCost h| ≤
      |ε| * Ω * |Q.gridSignedCost h - R.gridSignedCost h| := by
  have hq := Q.gridCost_affine_difference W V hV hW
  have hr := R.gridCost_affine_difference W V hV hW
  change Q.gridCost W - Q.gridCost V = ε * Ω * Q.gridSignedCost h at hq
  change R.gridCost W - R.gridCost V = ε * Ω * R.gridSignedCost h at hr
  have hp : 0 ≤ |ε| * Ω * |Q.gridSignedCost h - R.gridSignedCost h| := by positivity
  have hlo := neg_abs_le (ε * Ω * (Q.gridSignedCost h - R.gridSignedCost h))
  rw [abs_mul, abs_mul, abs_of_pos hΩ] at hlo
  apply abs_le.mpr
  constructor
  · nlinarith [hR Q]
  · linarith [hQ R]

theorem gridIFTBranch_nodes_lipschitz (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ M δ : ℝ, 0 < M ∧ 0 < δ ∧ ∀ ε : ℝ, |ε| < δ → ∀ v : Fin (n + 2),
      |cdfNode (gridIFTBranch h hh Ω hΩ ε) v - (v.val : ℝ) / ((n : ℝ) + 1)| ≤ M * |ε| := by
  obtain ⟨C, δ, hC, hδ, hb⟩ := gridIFTBranch_nodes_expansion (n := n) h hh Ω hΩ
  let r := nodalStrength (deriv (gridIFTBranch (n := n) h hh Ω hΩ) 0)
  refine ⟨C + ‖r‖, min δ 1, by positivity, lt_min hδ zero_lt_one, ?_⟩
  intro ε hε v
  have he := hb ε (lt_of_lt_of_le hε (min_le_left δ 1)) v
  have he1 : |ε| < 1 := lt_of_lt_of_le hε (min_le_right δ 1)
  have hr : |r v| ≤ ‖r‖ := norm_le_pi_norm r v
  have hs : ε ^ 2 ≤ |ε| := by nlinarith [sq_abs ε, abs_nonneg ε]
  have ha := abs_add_le
    (cdfNode (gridIFTBranch h hh Ω hΩ ε) v - (v.val : ℝ) / ((n : ℝ) + 1) - ε * r v)
    (ε * r v)
  rw [sub_add_cancel, abs_mul] at ha
  have hm := mul_le_mul_of_nonneg_left hr (abs_nonneg ε)
  have hc := mul_le_mul_of_nonneg_left hs hC.le
  change |cdfNode (gridIFTBranch h hh Ω hΩ ε) v - ↑↑v / (↑n + 1) - ε * r v| ≤ C * ε ^ 2 at he
  nlinarith

end TimeTraps.Interval
