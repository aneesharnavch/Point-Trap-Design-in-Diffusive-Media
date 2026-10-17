module

public import TimeTraps.Analysis.GraphSobolevSpace
public import TimeTraps.Analysis.IntervalDirichletDense

@[expose] public section

/-! Density follows from the product of the full edge H1 spaces whose
two endpoint traces vanish. Such edge families satisfy every vertex trace
constraint, and their states are dense in the original edge L2 product. -/

namespace TimeTraps.Analysis

open Set TimeTraps.Graph IntervalSobolevSpace

variable {V E : Type*}

noncomputable def graphZeroEdgeBoundary (G : MetricGraph V E) (e : E) :
    IntervalDirichletBoundary 0 (G.length e) := by
  classical
  exact {
    interval_pos := G.length_pos e
    zero_sites := {0, G.length e}
    nonempty := by simp
    boundary_only := by intro z hz; simpa using hz
  }

noncomputable def graphSobolevZeroFamily (G : MetricGraph V E)
    (u : ∀ e, IntervalDirichletSpace (graphZeroEdgeBoundary G e)) : GraphSobolevSpace G := by
  let U : GraphSobolevProduct G := WithLp.toLp 2 (fun e => (u e).val)
  refine ⟨U, (graphSobolevSubspace_mem_iff G U).mpr ?_⟩
  have hz (a : E ⊕ E) : graphEndpointTraceL G a U = 0 := by
    cases a with
    | inl e =>
        exact ((graphZeroEdgeBoundary G e).subspace_mem_iff (u e).val).mp (u e).property 0
          (by simp [graphZeroEdgeBoundary])
    | inr e =>
        exact ((graphZeroEdgeBoundary G e).subspace_mem_iff (u e).val).mp (u e).property (G.length e)
          (by simp [graphZeroEdgeBoundary])
  intro a b _
  rw [hz a, hz b]

theorem graphSobolevZeroFamily_state (G : MetricGraph V E)
    (u : ∀ e, IntervalDirichletSpace (graphZeroEdgeBoundary G e)) (e : E) :
    (graphSobolevSpaceStateL G (graphSobolevZeroFamily G u)) e =
      (graphZeroEdgeBoundary G e).stateL (u e) := rfl

theorem graphSobolevSpaceStateL_denseRange (G : MetricGraph V E) :
    DenseRange (graphSobolevSpaceStateL G) := by
  let T := (PiLp.continuousLinearEquiv 2 ℝ
    (fun e : E => IntervalSobolevL2 0 (G.length e))).symm
  let F : (∀ e, IntervalDirichletSpace (graphZeroEdgeBoundary G e)) → GraphL2Product G :=
    fun u => T (fun e => (graphZeroEdgeBoundary G e).stateL (u e))
  have hF : DenseRange F := T.surjective.denseRange.comp
    (DenseRange.piMap (fun e => (graphZeroEdgeBoundary G e).stateL_denseRange)) T.continuous
  apply Dense.mono (s₁ := Set.range F) ?_ hF
  rintro _ ⟨u, rfl⟩
  exact ⟨graphSobolevZeroFamily G u, rfl⟩

end TimeTraps.Analysis
