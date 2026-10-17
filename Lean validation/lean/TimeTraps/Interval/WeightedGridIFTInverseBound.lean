module

public import TimeTraps.Interval.WeightedGridIFTGlobal

@[expose] public section

/-! A quantitative local inverse estimate in grid coordinates, uniform in
the common perturbation parameter. Only the affine residual is differentiated. -/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology ContDiff

variable {n : ℕ}

theorem gridIFTResidual_inverse_bound (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω) :
    ∃ C : ℝ, 0 < C ∧ ∃ U : Set (ℝ × (Fin n → ℝ)), IsOpen U ∧
      ((0 : ℝ), gridIFTBaseline n) ∈ U ∧
      ∀ (ε : ℝ) (p q : Fin n → ℝ), (ε, p) ∈ U → (ε, q) ∈ U →
        ‖p - q‖ ≤ C * ‖gridIFTResidual h Ω (ε, p) - gridIFTResidual h Ω (ε, q)‖ := by
  let E := (weightedGridUniformJacobianEquiv n Ω hΩ).toContinuousLinearEquiv
  let B : ℝ := ‖E.symm.toContinuousLinearMap‖ + 1
  have hB : 0 < B := by dsimp only [B]; positivity
  have hinv (r : Fin n → ℝ) : ‖r‖ ≤ B * ‖weightedGridUniformJacobian n Ω r‖ := by
    have hb := E.symm.toContinuousLinearMap.le_opNorm (E r)
    simp only [ContinuousLinearEquiv.coe_coe, E.symm_apply_apply] at hb
    change ‖r‖ ≤ ‖E.symm.toContinuousLinearMap‖ * ‖weightedGridUniformJacobian n Ω r‖ at hb
    exact hb.trans (by dsimp only [B]; nlinarith [norm_nonneg (weightedGridUniformJacobian n Ω r)])
  let L := fderiv ℝ (gridIFTResidual h Ω) (0, gridIFTBaseline n)
  have hc := (gridIFTResidual_contDiffAt h hh Ω (0, gridIFTBaseline n)
    gridIFTBaseline_midpoints).hasStrictFDerivAt (by norm_num)
  have he := hc.isLittleO.def (show (0 : ℝ) < 1 / (2 * B) by positivity)
  obtain ⟨u, v, hu, h0u, hv, h0v, huv⟩ := mem_nhds_prod_iff'.mp he
  refine ⟨2 * B, mul_pos (by norm_num) hB, u ∩ v, hu.inter hv, ⟨h0u, h0v⟩, ?_⟩
  intro ε p q hp hq
  have hb := huv (show ((ε, p), (ε, q)) ∈ u ×ˢ v from ⟨hp.1, hq.2⟩)
  have hL : L (0, p - q) = weightedGridUniformJacobian n Ω (p - q) := by
    have hi := congrArg (fun f : (Fin n → ℝ) →L[ℝ] (Fin n → ℝ) => f (p - q))
      (gridIFTResidual_fderiv_grid h hh Ω)
    exact hi
  have hd : (ε, p) - (ε, q) = ((0 : ℝ), p - q) := by ext <;> simp
  change ‖gridIFTResidual h Ω (ε, p) - gridIFTResidual h Ω (ε, q) -
      L ((ε, p) - (ε, q))‖ ≤ (1 / (2 * B)) * ‖(ε, p) - (ε, q)‖ at hb
  rw [hd, hL, Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)] at hb
  have ht : ‖weightedGridUniformJacobian n Ω (p - q)‖ ≤
      ‖gridIFTResidual h Ω (ε, p) - gridIFTResidual h Ω (ε, q)‖ +
      ‖gridIFTResidual h Ω (ε, p) - gridIFTResidual h Ω (ε, q) -
        weightedGridUniformJacobian n Ω (p - q)‖ := by
    calc
      _ = ‖(gridIFTResidual h Ω (ε, p) - gridIFTResidual h Ω (ε, q)) -
          (gridIFTResidual h Ω (ε, p) - gridIFTResidual h Ω (ε, q) -
            weightedGridUniformJacobian n Ω (p - q))‖ := by congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hi := hinv (p - q)
  have hm := mul_le_mul_of_nonneg_left ht hB.le
  have hb' := mul_le_mul_of_nonneg_left hb hB.le
  have heq : B * (1 / (2 * B)) = (1 / 2 : ℝ) := by field_simp
  rw [← mul_assoc, heq] at hb'
  nlinarith

end TimeTraps.Interval
