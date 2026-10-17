module

public import TimeTraps.Analysis.GraphHeatPointResolventWeak
public import TimeTraps.Probability.GraphPhysicalSpeed

@[expose] public section

/-! The original per-edge speed density as an actual edge L2 source.
It has no imposed equality between incident-edge traces. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter InnerProductSpace IntervalSobolevSpace

variable {V E : Type*}

noncomputable def graphPhysicalSourceEdge (G : MetricGraph V E) (e : E) :
    C(Icc (0 : ℝ) (G.length e), ℝ) :=
  ⟨fun x => G.source e x.val, (G.source_continuous e).domRestrict⟩

noncomputable def graphPhysicalSourceL2 (G : MetricGraph V E) : GraphL2Product G :=
  WithLp.toLp 2 (fun e => continuousL2 (G.length_pos e) (graphPhysicalSourceEdge G e))

theorem graphPhysicalSourceL2_ae (G : MetricGraph V E) (e : E) :
    graphPhysicalSourceL2 G e =ᵐ[volume.restrict (Ioo (0 : ℝ) (G.length e))] G.source e := by
  filter_upwards [continuousL2_ae (G.length_pos e) (graphPhysicalSourceEdge G e),
    ae_restrict_mem measurableSet_Ioo] with x hx hm
  change (continuousL2 (G.length_pos e) (graphPhysicalSourceEdge G e)) x = G.source e x
  rw [hx]
  change G.source e (projIcc 0 (G.length e) (G.length_pos e).le x).val = _
  rw [projIcc_of_mem (G.length_pos e).le (Ioo_subset_Icc_self hm)]

theorem graphPhysicalSourceL2_physicalSpeed_ae [Fintype E] (G : MetricGraph V E)
    (b : ℝ) (e : E) :
    graphPhysicalSourceL2 G e =ᵐ[volume.restrict (Ioo (0 : ℝ) (G.length e))]
      (fun y => G.physicalSpeed b (G.edgePointClamped e y)) := by
  filter_upwards [graphPhysicalSourceL2_ae G e, ae_restrict_mem measurableSet_Ioo] with y hy hm
  rw [hy]
  change G.source e y = G.physicalSpeed b
    (G.edgePoint e (projIcc 0 (G.length e) (G.length_pos e).le y))
  rw [projIcc_of_mem (G.length_pos e).le (Ioo_subset_Icc_self hm)]
  exact (G.physicalSpeed_openEdge b e ⟨y, hm⟩).symm

theorem GraphShiftedContactOperatorProblem.operatorLoad_physicalSource [Fintype E]
    (P : GraphShiftedContactOperatorProblem V E) {U : V → ℝ} {u : E → ℝ → ℝ}
    (hu : GraphEnergy P.geometry U u) :
    P.operatorLoad (graphPhysicalSourceL2 P.geometry) (graphSobolevSpaceOfEnergy P.geometry hu) =
      ∑ e, ∫ x in (0 : ℝ)..P.geometry.length e, P.geometry.source e x * u e x := by
  rw [P.operatorLoad_ofEnergy]
  apply Finset.sum_congr rfl
  intro e _
  rw [intervalIntegral.integral_of_le (P.geometry.length_pos e).le,
    intervalIntegral.integral_of_le (P.geometry.length_pos e).le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [graphPhysicalSourceL2_ae P.geometry e] with x hx
  rw [hx]

end TimeTraps.Analysis
