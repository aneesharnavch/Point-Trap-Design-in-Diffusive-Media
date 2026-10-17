module

public import TimeTraps.Probability.GraphPhysicalSpeedMeasure
public import TimeTraps.Graph.MetricCost

@[expose] public section

/-! The speed measure has the literal original edge densities, total
source mass, and no vertex atoms. Neither matching density traces nor
global continuity of the Borel speed representative is used. -/

namespace TimeTraps.Graph

open Set MeasureTheory Filter TimeTraps.Analysis
open scoped ENNReal NNReal BigOperators

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem MetricGraph.physicalSpeedMeasure_integral_edges (G : MetricGraph V E)
    {f : GraphRealization G → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ p, ‖f p‖ ≤ C) :
    (∫ p, f p ∂G.physicalSpeedMeasure) =
      ∑ e, ∫ r in (0 : ℝ)..G.length e,
        G.source e r * f (G.edgePointClamped e r) := by
  let F := fun p => G.physicalSpeed 1 p * f p
  have hm : Measurable F := (G.physicalSpeed_measurable 1).mul hf
  have hb (p) : ‖F p‖ ≤ (G.physicalSpeedUpper 1 zero_lt_one : ℝ) * C := by
    have hpos : 0 ≤ G.physicalSpeed 1 p :=
      (G.physicalSpeedLower 1 zero_lt_one).coe_nonneg.trans (G.physicalSpeed_bound 1 zero_lt_one p).1
    dsimp only [F]
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg hpos]
    exact mul_le_mul (G.physicalSpeed_bound 1 zero_lt_one p).2 (hC p)
      (norm_nonneg _) (G.physicalSpeedUpper 1 zero_lt_one).coe_nonneg
  have hi (e : E) : Integrable F (G.edgeLengthMeasure e) :=
    (integrable_const ((G.physicalSpeedUpper 1 zero_lt_one : ℝ) * C)).mono'
      hm.aestronglyMeasurable (Eventually.of_forall hb)
  rw [G.physicalSpeedMeasure_integral 1 zero_lt_one, MetricGraph.lengthMeasure,
    integral_finsetSum_measure (fun e _ => hi e)]
  apply Finset.sum_congr rfl
  intro e _
  rw [G.edgeLengthMeasure_integral e F hm,
    intervalIntegral.integral_of_le (G.length_pos e).le, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  dsimp only [F]
  rw [G.edgePointClamped_eq_openEdge e hr, G.physicalSpeed_openEdge]

theorem MetricGraph.physicalSpeedMeasure_integral_continuous (G : MetricGraph V E)
    (f : C(GraphRealization G, ℝ)) :
    (∫ p, f p ∂G.physicalSpeedMeasure) =
      ∑ e, ∫ r in (0 : ℝ)..G.length e,
        G.source e r * f (G.edgePointClamped e r) :=
  G.physicalSpeedMeasure_integral_edges f.continuous.measurable f.norm_coe_le_norm

theorem MetricGraph.physicalSpeedMeasure_mass_real (G : MetricGraph V E) :
    G.physicalSpeedMeasure.real univ = G.totalMass := by
  have he := G.physicalSpeedMeasure_integral_edges
    (f := fun _ => (1 : ℝ)) measurable_const (C := 1) (fun _ => by norm_num)
  simpa only [integral_const, smul_eq_mul, mul_one, MetricGraph.totalMass,
    sourcePrimitive] using he

theorem MetricGraph.physicalSpeedMeasure_mass (G : MetricGraph V E) :
    G.physicalSpeedMeasure univ = ENNReal.ofReal G.totalMass := by
  rw [← G.physicalSpeedMeasure_mass_real, Measure.real,
    ENNReal.ofReal_toReal (measure_ne_top _ _)]

theorem MetricGraph.physicalSpeedMeasure_vertices (G : MetricGraph V E) :
    G.physicalSpeedMeasure (range G.vertexPoint) = 0 :=
  withDensity_absolutelyContinuous G.lengthMeasure _ G.lengthMeasure_vertices

theorem MetricGraph.physicalSpeedMeasure_mass_pos (G : MetricGraph V E) :
    0 < G.physicalSpeedMeasure univ := by
  rw [G.physicalSpeedMeasure_mass]
  exact ENNReal.ofReal_pos.mpr G.totalMass_pos

end TimeTraps.Graph
