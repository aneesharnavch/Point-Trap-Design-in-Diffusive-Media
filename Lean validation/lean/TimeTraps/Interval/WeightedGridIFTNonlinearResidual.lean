module

public import TimeTraps.Interval.WeightedGridIFTInverseBound
public import TimeTraps.Interval.SourceDensityPerturbation

@[expose] public section

/-! Uniform weight errors control the affine residual at every actual
minimizer. A uniform first-order expansion also yields concentration near
the constant weight, without parameter differentiability assumptions. -/

namespace TimeTraps.Interval

open Set Filter MeasureTheory
open scoped Topology ContDiff

variable {n : ℕ}

theorem ClosedPartition.gridIFTResidual_error (Q : ClosedPartition (n + 1)) (W : CellWeight)
    (h : ℝ → ℝ) (hh : ContinuousOn h (Icc (0 : ℝ) 1)) (Ω ε δ : ℝ)
    (hδ : 0 ≤ δ) (hW : ∀ z ∈ Icc (0 : ℝ) 1, |Ω * (1 + ε * h z) - W.value z| ≤ δ)
    (hmin : ∀ P : ClosedPartition (n + 1), Q.gridCost W ≤ P.gridCost W) :
    ‖gridIFTResidual h Ω (ε, Q.gridIFTCoordinates)‖ ≤ δ := by
  apply (pi_norm_le_iff_of_nonneg hδ).mpr
  intro i
  obtain ⟨hl, hr⟩ := Q.gridIFTCoordinates_cells i
  let a := Q.canonicalCellNode i.castSucc.succ.castSucc
  let b := Q.canonicalCellNode i.castSucc.succ.succ
  let q := Q.point i.castSucc.succ
  have ha : a ∈ Icc (0 : ℝ) 1 := Q.canonicalCellNode_mem _
  have hb : b ∈ Icc (0 : ℝ) 1 := Q.canonicalCellNode_mem _
  have hq : q ∈ Icc (0 : ℝ) 1 := Q.point_mem _
  have hsub : uIcc a b ⊆ Icc (0 : ℝ) 1 :=
    fun _ hz => ⟨(le_min ha.1 hb.1).trans hz.1, hz.2.trans (max_le ha.2 hb.2)⟩
  have hiW : IntervalIntegrable (fun z => W.value z * (q - z)) volume a b :=
    ((W.continuous.mul (continuousOn_const.sub continuousOn_id)).mono hsub).intervalIntegrable
  have hiA : IntervalIntegrable (fun z => Ω * (1 + ε * h z) * (q - z)) volume a b :=
    (((continuousOn_const.mul (continuousOn_const.add (continuousOn_const.mul hh))).mul
      (continuousOn_const.sub continuousOn_id)).mono hsub).intervalIntegrable
  have he : gridIFTResidual h Ω (ε, Q.gridIFTCoordinates) i =
      ∫ z in a..b, (Ω * (1 + ε * h z) - W.value z) * (q - z) := by
    rw [gridIFTResidual_eq_integral h hh Ω ε Q.gridIFTCoordinates i
      (hl.symm ▸ ha) (hr.symm ▸ hb), hl, hr]
    change (∫ z in a..b, Ω * (1 + ε * h z) * (q - z)) = _
    have hz : (∫ z in a..b, W.value z * (q - z)) = 0 := Q.grid_centroid_residual W hmin i
    calc
      _ = (∫ z in a..b, Ω * (1 + ε * h z) * (q - z)) -
          ∫ z in a..b, W.value z * (q - z) := by rw [hz, sub_zero]
      _ = _ := by
        rw [← intervalIntegral.integral_sub hiA hiW]
        apply intervalIntegral.integral_congr
        intro z _
        dsimp only
        ring
  rw [he]
  have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := a) (b := b) (f := fun z => (Ω * (1 + ε * h z) - W.value z) * (q - z)) (C := δ) (fun z hz => ?_)
  · have hab : |b - a| ≤ 1 := abs_le.mpr ⟨by linarith [ha.2, hb.1], by linarith [ha.1, hb.2]⟩
    exact hbound.trans ((mul_le_mul_of_nonneg_left hab hδ).trans_eq (mul_one δ))
  · have hz' : z ∈ Icc (0 : ℝ) 1 := hsub ⟨hz.1.le, hz.2⟩
    have hqz : |q - z| ≤ 1 := abs_le.mpr ⟨by linarith [hq.1, hz'.2], by linarith [hq.2, hz'.1]⟩
    rw [Real.norm_eq_abs, abs_mul]
    exact (mul_le_mul (hW z hz') hqz (abs_nonneg _) hδ).trans_eq (mul_one δ)

theorem gridIFT_nonlinear_weights_near (W : ℝ → CellWeight) (h : ℝ → ℝ)
    (hh : ContinuousOn h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)
    (hexp : SourceUniformExpansion (fun ε => (W ε).value) (fun _ => Ω) (fun z => Ω * h z))
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ z ∈ Icc (0 : ℝ) 1, |(W ε).value z - Ω| ≤ δ := by
  obtain ⟨B, hB, hrem⟩ := hexp
  obtain ⟨H, hH⟩ := isCompact_Icc.exists_bound_of_continuousOn hh
  have hc : Continuous (fun ε : ℝ => B * ε ^ 2 + |ε| * Ω * H) := by fun_prop
  have he : ∀ᶠ ε in 𝓝 (0 : ℝ), B * ε ^ 2 + |ε| * Ω * H < δ :=
    (tendsto_order.mp (hc.tendsto 0)).2 δ (by simpa using hδ)
  filter_upwards [hrem, he] with ε hε heε
  intro z hz
  have hr := hε z hz
  have hp : |ε * (Ω * h z)| ≤ |ε| * Ω * H := by
    rw [abs_mul, abs_mul, abs_of_pos hΩ, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using hH z hz)
      (mul_nonneg (abs_nonneg ε) hΩ.le)
  have ha := abs_add_le ((W ε).value z - Ω - ε * (Ω * h z)) (ε * (Ω * h z))
  rw [sub_add_cancel] at ha
  exact (ha.trans (add_le_add hr hp)).trans heε.le

end TimeTraps.Interval
