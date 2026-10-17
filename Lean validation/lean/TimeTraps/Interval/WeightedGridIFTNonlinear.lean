module

public import TimeTraps.Interval.WeightedGridIFTNonlinearResidual
public import TimeTraps.Interval.WeightedGridIFTTaylorDesign

@[expose] public section

/-! Every global optimizer for a family with a uniform quadratic weight
remainder lies within O(ε²) of the affine IFT branch. No differentiability
in ε is required of the actual weight family or its optimizer selections. -/

namespace TimeTraps.Interval

open Set Filter
open scoped Topology ContDiff

variable {n : ℕ}

theorem gridIFT_nonlinear_minimizers_compare (W : ℝ → CellWeight) (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)
    (hexp : SourceUniformExpansion (fun ε => (W ε).value) (fun _ => Ω) (fun z => Ω * h z)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ Q : ClosedPartition (n + 1),
      (∀ P : ClosedPartition (n + 1), Q.gridCost (W ε) ≤ P.gridCost (W ε)) →
      ‖Q.gridIFTCoordinates - gridIFTBranch h hh Ω hΩ ε‖ ≤ C * ε ^ 2 := by
  obtain ⟨C, hC, U, hU, h0U, hinv⟩ := gridIFTResidual_inverse_bound (n := n) h hh Ω hΩ
  obtain ⟨u, v, hu, h0u, hv, h0v, huv⟩ := mem_nhds_prod_iff'.mp (hU.mem_nhds h0U)
  let V : CellWeight := ⟨fun _ => Ω, continuousOn_const, fun _ _ => hΩ⟩
  obtain ⟨δ, hδ, hnear⟩ := weighted_grid_minimizers_near_uniform V (Nat.succ_pos n) hΩ
    (fun _ _ => rfl) (ClosedPartition.gridIFTCoordinates ⁻¹' v)
    (hv.preimage ClosedPartition.gridIFTCoordinates_continuous)
    (by simpa only [mem_preimage, ClosedPartition.gridIFTCoordinates_uniform] using h0v)
  have hclose := gridIFT_nonlinear_weights_near W h hh.continuousOn Ω hΩ hexp hδ
  have hparam : ∀ᶠ ε in 𝓝 (0 : ℝ), ε ∈ u := hu.mem_nhds h0u
  have hc : ContinuousAt (fun ε : ℝ => (ε, gridIFTBranch (n := n) h hh Ω hΩ ε)) 0 :=
    continuousAt_id.prodMk (gridIFTBranch_contDiffAt h hh Ω hΩ).continuousAt
  have hbranch : ∀ᶠ ε in 𝓝 (0 : ℝ), (ε, gridIFTBranch (n := n) h hh Ω hΩ ε) ∈ U :=
    hc.eventually (hU.mem_nhds (by simpa only [gridIFTBranch_zero] using h0U))
  obtain ⟨B, hB, hrem⟩ := hexp
  refine ⟨C * B + 1, by positivity, ?_⟩
  filter_upwards [hclose, hparam, hbranch, hrem, gridIFTBranch_residual (n := n) h hh Ω hΩ]
    with ε hcloseε hparamε hbranchε hremε hzeroε
  intro Q hQ
  have hQv : Q.gridIFTCoordinates ∈ v := hnear (W ε) hcloseε Q hQ
  have hQU : (ε, Q.gridIFTCoordinates) ∈ U := huv ⟨hparamε, hQv⟩
  have hres := Q.gridIFTResidual_error (W ε) h hh.continuousOn Ω ε (B * ε ^ 2)
    (mul_nonneg hB (sq_nonneg ε)) (fun z hz => ?_) hQ
  · have hi := hinv ε Q.gridIFTCoordinates (gridIFTBranch h hh Ω hΩ ε) hQU hbranchε
    rw [hzeroε, sub_zero] at hi
    exact hi.trans ((mul_le_mul_of_nonneg_left hres hC.le).trans (by nlinarith [sq_nonneg ε]))
  · have he : Ω * (1 + ε * h z) - (W ε).value z =
        -((W ε).value z - Ω - ε * (Ω * h z)) := by ring
    rw [he, abs_neg]
    exact hremε z hz

theorem ClosedPartition.gridIFTCoordinates_node_bound (Q : ClosedPartition (n + 1))
    (p : Fin n → ℝ) (v : Fin (n + 2)) :
    |Q.point v - cdfNode p v| ≤ ‖Q.gridIFTCoordinates - p‖ := by
  rw [← Q.gridIFTCoordinates_nodes]
  refine Fin.cases ?_ (fun k => ?_) v
  · simp only [cdfNode_first, sub_self, abs_zero]
    exact norm_nonneg _
  · refine Fin.lastCases ?_ (fun i => ?_) k
    · change |cdfNode _ (Fin.last (n + 1)) - cdfNode _ (Fin.last (n + 1))| ≤ _
      simp only [cdfNode_last, sub_self, abs_zero]
      exact norm_nonneg _
    · simp only [cdfNode_site]
      exact norm_le_pi_norm (Q.gridIFTCoordinates - p) i

theorem gridIFT_nonlinear_nodes_compare (W : ℝ → CellWeight) (h : ℝ → ℝ)
    (hh : ContDiffOn ℝ 1 h (Icc (0 : ℝ) 1)) (Ω : ℝ) (hΩ : 0 < Ω)
    (hexp : SourceUniformExpansion (fun ε => (W ε).value) (fun _ => Ω) (fun z => Ω * h z)) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ ε in 𝓝 (0 : ℝ), ∀ Q : ClosedPartition (n + 1),
      (∀ P : ClosedPartition (n + 1), Q.gridCost (W ε) ≤ P.gridCost (W ε)) →
      ∀ v : Fin (n + 2), |Q.point v - cdfNode (gridIFTBranch h hh Ω hΩ ε) v| ≤ C * ε ^ 2 := by
  obtain ⟨C, hC, hb⟩ := gridIFT_nonlinear_minimizers_compare (n := n) W h hh Ω hΩ hexp
  refine ⟨C, hC, hb.mono ?_⟩
  intro ε hε Q hQ v
  exact (Q.gridIFTCoordinates_node_bound _ v).trans (hε Q hQ)

end TimeTraps.Interval
