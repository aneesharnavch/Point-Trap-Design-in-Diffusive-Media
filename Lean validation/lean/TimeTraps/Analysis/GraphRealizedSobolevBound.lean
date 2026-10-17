module

public import TimeTraps.Analysis.GraphRealizedSobolev
public import TimeTraps.Analysis.IntervalSobolevCompactEmbedding

@[expose] public section

/-! The continuous graph representative is a bounded linear map from
the actual H1 space, with its bound derived from the finite edge embeddings. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Graph IntervalSobolevSpace

variable {V E : Type*} [Fintype E] [Nonempty E]

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

noncomputable local instance graphRealizationNormedSpace (G : MetricGraph V E) :
    NormedSpace ℝ (GraphSobolevSpace G) := Submodule.normedSpace (graphSobolevSubspace G)

noncomputable def graphRealizedEdgeL (G : MetricGraph V E) (e : E) :
    GraphSobolevSpace G →L[ℝ] C(Icc (0 : ℝ) (G.length e), ℝ) :=
  (toContinuousL (G.length_pos e)).comp
    ((graphSobolevComponentL G e).comp (graphSobolevSubspace G).subtypeL)

omit [Fintype E] [Nonempty E] in
theorem graphRealizedEdgeL_apply (G : MetricGraph V E) (e : E)
    (u : GraphSobolevSpace G) (x : Icc (0 : ℝ) (G.length e)) :
    graphRealizedEdgeL G e u x = graphSobolevRepresentative G u.val e x.val := rfl

theorem graphRealizedSobolev_add (G : MetricGraph V E) (u v : GraphSobolevSpace G) :
    graphRealizedSobolev G (u + v) = graphRealizedSobolev G u + graphRealizedSobolev G v := by
  ext z
  obtain ⟨e, x, rfl⟩ := G.edgePoint_surjective z
  change graphRealizedSobolev G (u + v) (G.edgePoint e x) =
    graphRealizedSobolev G u (G.edgePoint e x) + graphRealizedSobolev G v (G.edgePoint e x)
  simp only [graphRealizedSobolev_edge, ← graphRealizedEdgeL_apply, map_add,
    ContinuousMap.add_apply]

theorem graphRealizedSobolev_smul (G : MetricGraph V E) (c : ℝ) (u : GraphSobolevSpace G) :
    graphRealizedSobolev G (c • u) = c • graphRealizedSobolev G u := by
  ext z
  obtain ⟨e, x, rfl⟩ := G.edgePoint_surjective z
  change graphRealizedSobolev G (c • u) (G.edgePoint e x) =
    c * graphRealizedSobolev G u (G.edgePoint e x)
  simp only [graphRealizedSobolev_edge, ← graphRealizedEdgeL_apply, map_smul,
    ContinuousMap.smul_apply, smul_eq_mul]

theorem graphRealizedSobolev_norm_bound (G : MetricGraph V E) (u : GraphSobolevSpace G) :
    ‖graphRealizedSobolev G u‖ ≤ (∑ e, ‖graphRealizedEdgeL G e‖) * ‖u‖ := by
  have hbound : 0 ≤ (∑ e, ‖graphRealizedEdgeL G e‖) * ‖u‖ :=
    mul_nonneg (Finset.sum_nonneg (fun e _ => norm_nonneg (graphRealizedEdgeL G e))) (norm_nonneg u)
  apply (ContinuousMap.norm_le (graphRealizedSobolev G u) hbound).mpr
  intro z
  obtain ⟨e, x, rfl⟩ := G.edgePoint_surjective z
  rw [graphRealizedSobolev_edge, ← graphRealizedEdgeL_apply]
  calc
    _ ≤ ‖graphRealizedEdgeL G e u‖ := ContinuousMap.norm_coe_le_norm _ x
    _ ≤ ‖graphRealizedEdgeL G e‖ * ‖u‖ := (graphRealizedEdgeL G e).le_opNorm u
    _ ≤ _ := mul_le_mul_of_nonneg_right
      (Finset.single_le_sum (fun d _ => norm_nonneg (graphRealizedEdgeL G d)) (Finset.mem_univ e))
        (norm_nonneg u)

noncomputable def graphRealizedSobolevL (G : MetricGraph V E) :
    GraphSobolevSpace G →L[ℝ] C(GraphRealization G, ℝ) :=
  ({ toFun := graphRealizedSobolev G
     map_add' := graphRealizedSobolev_add G
     map_smul' := graphRealizedSobolev_smul G } :
    GraphSobolevSpace G →ₗ[ℝ] C(GraphRealization G, ℝ)).mkContinuous
      (∑ e, ‖graphRealizedEdgeL G e‖) (graphRealizedSobolev_norm_bound G)

theorem graphRealizedSobolevL_apply (G : MetricGraph V E) (u : GraphSobolevSpace G) :
    graphRealizedSobolevL G u = graphRealizedSobolev G u := rfl

end TimeTraps.Analysis
