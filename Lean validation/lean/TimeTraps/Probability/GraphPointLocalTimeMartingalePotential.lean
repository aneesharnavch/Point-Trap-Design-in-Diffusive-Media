module

public import TimeTraps.Analysis.GraphHeatPointPotentialBumpOccupation

@[expose] public section

/-! The actual point potential as a continuous graph state and the
uniform-norm convergence of the true normalized occupation potentials. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal Topology

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable def GraphShiftedContactOperatorProblem.pointMartingalePotentialState
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (T : ℝ) :
    C(GraphRealization P.geometry, ℝ) := by
  have hc := P.realizedHeatPointPotential_joint_continuous.comp
    (show Continuous (fun x : GraphRealization P.geometry => ((x, a), T)) from
      (continuous_id.prodMk continuous_const).prodMk continuous_const)
  exact ⟨fun x => P.realizedHeatPointPotential x a T, hc⟩

theorem GraphShiftedContactOperatorProblem.pointMartingalePotentialState_apply
    (P : GraphShiftedContactOperatorProblem V E) (a x : GraphRealization P.geometry) (T : ℝ) :
    P.pointMartingalePotentialState a T x = P.realizedHeatPointPotential x a T := rfl

theorem GraphShiftedContactOperatorProblem.pointMartingalePotentialState_tendsto
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) {T : ℝ} (hT : 0 ≤ T)
    {r : ℕ → ℝ} (hr : ∀ n, 0 < r n) (hr0 : Tendsto r atTop (𝓝 0)) :
    Tendsto (fun n => P.occupationPotential (P.geometry.pointBump a (r n)) T) atTop
      (𝓝 (P.pointMartingalePotentialState a T)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨δ, hδ, hd⟩ := P.occupationPotential_pointBump_compact_uniform T (half_pos hε)
  filter_upwards [hr0.eventually (gt_mem_nhds hδ)] with n hn
  rw [dist_eq_norm]
  apply lt_of_le_of_lt _ (half_lt_self hε)
  apply (ContinuousMap.norm_le _ (half_pos hε).le).mpr
  intro x
  simpa only [ContinuousMap.sub_apply, pointMartingalePotentialState_apply, Real.norm_eq_abs] using
    (hd (r n) (hr n) hn T ⟨hT, le_rfl⟩ x a).le

end TimeTraps.Analysis
