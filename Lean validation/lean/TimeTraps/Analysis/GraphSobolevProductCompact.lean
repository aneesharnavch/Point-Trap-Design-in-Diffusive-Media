module

public import TimeTraps.Analysis.GraphSobolevProduct
public import TimeTraps.Analysis.IntervalSobolevCompactL2

@[expose] public section

/-! The edge state inclusion is compact for the genuine finite Hilbert
product. A unit ball has each edge component in its edge unit ball, whose
state image is contained in a compact set. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Graph IntervalSobolevSpace

variable {V E : Type*} [Fintype E]

theorem graphSobolevStateL_compact (G : MetricGraph V E) :
    IsCompactOperator (graphSobolevStateL G) := by
  classical
  have hK : ∀ e : E, ∃ K : Set (IntervalSobolevL2 0 (G.length e)),
      IsCompact K ∧ (IntervalSobolevSpace.stateL 0 (G.length e)) ''
        Metric.closedBall 0 1 ⊆ K := fun e =>
    (stateL_isCompact (G.length_pos e)).image_closedBall_subset_compact 1
  choose K hcompact hsubset using hK
  let T := (PiLp.continuousLinearEquiv 2 ℝ
    (fun e : E => IntervalSobolevL2 0 (G.length e))).symm
  apply (isCompactOperator_iff_exists_mem_nhds_image_subset_compact
    (graphSobolevStateL G)).mpr
  refine ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ zero_lt_one,
    T '' Set.pi Set.univ K, (isCompact_univ_pi hcompact).image T.continuous, ?_⟩
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨fun e => (u e).state, ?_, rfl⟩
  intro e _
  apply hsubset e
  refine ⟨u e, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hu ⊢
  exact (PiLp.norm_apply_le u e).trans hu

end TimeTraps.Analysis
