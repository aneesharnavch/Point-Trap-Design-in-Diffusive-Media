module

public import TimeTraps.Analysis.GraphRobinResolventPointwise
public import TimeTraps.Probability.GraphPhysicalSpeedBounds

@[expose] public section

/-! The resolvent forcing is literally the realized weak state plus the
original Borel physical speed. Its independent edge L2 representative
is exact, without any matching assumption on rho at vertices. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter InnerProductSpace

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem graphRobinResolventForcing_measurable (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) (b : ℝ) :
    Measurable (fun x => graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu) x + G.physicalSpeed b x) :=
  (graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu)).continuous.measurable.add
    (G.physicalSpeed_measurable b)

omit [Fintype V] in
theorem graphRobinResolventForcing_bounded (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) (b : ℝ) (hb : 0 < b) :
    ∃ C : ℝ, ∀ x, ‖graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu) x + G.physicalSpeed b x‖ ≤ C := by
  refine ⟨‖graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu)‖ + (G.physicalSpeedUpper b hb : ℝ), ?_⟩
  intro x
  have hs := G.physicalSpeed_bound b hb x
  have hn : 0 ≤ G.physicalSpeed b x := (G.physicalSpeedLower b hb).coe_nonneg.trans hs.1
  calc
    _ ≤ ‖graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu) x‖ + ‖G.physicalSpeed b x‖ := norm_add_le _ _
    _ ≤ _ := add_le_add (ContinuousMap.norm_coe_le_norm _ x)
      (by rw [Real.norm_eq_abs, abs_of_nonneg hn]; exact hs.2)

omit [Fintype V] in
theorem graphRobinResolventForcing_ae (G : MetricGraph V E)
    {U : V → ℝ} {u : E → ℝ → ℝ} (hu : GraphEnergy G U u) (b : ℝ) (e : E) :
    (graphSobolevSpaceStateL G (graphSobolevSpaceOfEnergy G hu) + graphPhysicalSourceL2 G) e
      =ᵐ[volume.restrict (Ioo (0 : ℝ) (G.length e))]
      (fun y => graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu) (G.edgePointClamped e y) +
        G.physicalSpeed b (G.edgePointClamped e y)) := by
  filter_upwards [Lp.coeFn_add
      ((graphSobolevSpaceStateL G (graphSobolevSpaceOfEnergy G hu)) e) (graphPhysicalSourceL2 G e),
    graphSobolevSpaceOfEnergy_state_ae G hu e, graphPhysicalSourceL2_physicalSpeed_ae G b e,
    ae_restrict_mem measurableSet_Ioo] with y hadd hstate hsource hy
  change (((graphSobolevSpaceStateL G (graphSobolevSpaceOfEnergy G hu)) e) + graphPhysicalSourceL2 G e) y = _
  rw [hadd]
  change ((graphSobolevSpaceStateL G (graphSobolevSpaceOfEnergy G hu)) e) y +
    (graphPhysicalSourceL2 G e) y = _
  rw [hstate, hsource]
  congr 1
  change u e y = graphRealizedSobolev G (graphSobolevSpaceOfEnergy G hu)
    (G.edgePoint e (projIcc 0 (G.length e) (G.length_pos e).le y))
  rw [graphRealizedSobolev_ofEnergy, projIcc_of_mem (G.length_pos e).le (Ioo_subset_Icc_self hy)]

end TimeTraps.Analysis
