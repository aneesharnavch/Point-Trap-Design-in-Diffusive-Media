module

public import TimeTraps.Graph.TopologicalRealizationMeasurable
public import Mathlib.MeasureTheory.Integral.Bochner.Basic

@[expose] public section

/-! Ordinary physical edge length as a finite Borel measure on the
realized graph. Each open edge is pushed through its original length
coordinate; summation counts each labeled edge once. -/

namespace TimeTraps.Graph

open Set MeasureTheory
open scoped ENNReal

variable {V E : Type*} [Fintype V] [Fintype E]

noncomputable def MetricGraph.edgePointClamped (G : MetricGraph V E) (e : E)
    (x : ℝ) : GraphRealization G := G.edgePoint e (projIcc 0 (G.length e) (G.length_pos e).le x)

omit [Fintype V] [Fintype E] in
theorem MetricGraph.edgePointClamped_continuous (G : MetricGraph V E) (e : E) :
    Continuous (G.edgePointClamped e) := (G.edgePoint_continuous e).comp continuous_projIcc

theorem MetricGraph.edgePointClamped_measurable (G : MetricGraph V E) (e : E) :
    Measurable (G.edgePointClamped e) := (G.edgePointClamped_continuous e).measurable

noncomputable def MetricGraph.edgeLengthMeasure (G : MetricGraph V E) (e : E) :
    Measure (GraphRealization G) := (volume.restrict (Ioo 0 (G.length e))).map (G.edgePointClamped e)

instance graphEdgeLengthMeasure_finite (G : MetricGraph V E) (e : E) :
    IsFiniteMeasure (G.edgeLengthMeasure e) := inferInstanceAs (IsFiniteMeasure
      ((volume.restrict (Ioo 0 (G.length e))).map (G.edgePointClamped e)))

theorem MetricGraph.edgeLengthMeasure_mass (G : MetricGraph V E) (e : E) :
    G.edgeLengthMeasure e univ = ENNReal.ofReal (G.length e) := by
  rw [edgeLengthMeasure, Measure.map_apply (G.edgePointClamped_measurable e) MeasurableSet.univ]
  simp only [preimage_univ, Measure.restrict_apply MeasurableSet.univ, univ_inter,
    Real.volume_Ioo, sub_zero]

noncomputable def MetricGraph.lengthMeasure (G : MetricGraph V E) : Measure (GraphRealization G) :=
  ∑ e, G.edgeLengthMeasure e

instance graphLengthMeasure_finite (G : MetricGraph V E) : IsFiniteMeasure G.lengthMeasure :=
  inferInstanceAs (IsFiniteMeasure (∑ e, G.edgeLengthMeasure e))

theorem MetricGraph.lengthMeasure_mass (G : MetricGraph V E) :
    G.lengthMeasure univ = ∑ e, ENNReal.ofReal (G.length e) := by
  simp only [lengthMeasure, Measure.finsetSum_apply, G.edgeLengthMeasure_mass]

theorem MetricGraph.edgeLengthMeasure_lintegral (G : MetricGraph V E) (e : E)
    (f : GraphRealization G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂G.edgeLengthMeasure e) =
      ∫⁻ x in Ioo 0 (G.length e), f (G.edgePointClamped e x) :=
  lintegral_map hf (G.edgePointClamped_measurable e)

theorem MetricGraph.lengthMeasure_lintegral (G : MetricGraph V E)
    (f : GraphRealization G → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ p, f p ∂G.lengthMeasure) =
      ∑ e, ∫⁻ x in Ioo 0 (G.length e), f (G.edgePointClamped e x) := by
  simp only [lengthMeasure, lintegral_finsetSum_measure, G.edgeLengthMeasure_lintegral _ f hf]

theorem MetricGraph.edgeLengthMeasure_integral (G : MetricGraph V E) (e : E)
    (f : GraphRealization G → ℝ) (hf : Measurable f) :
    (∫ p, f p ∂G.edgeLengthMeasure e) =
      ∫ x in Ioo 0 (G.length e), f (G.edgePointClamped e x) :=
  integral_map (G.edgePointClamped_measurable e).aemeasurable hf.aestronglyMeasurable

theorem MetricGraph.lengthMeasure_integral (G : MetricGraph V E)
    (f : GraphRealization G → ℝ) (hf : Continuous f) :
    (∫ p, f p ∂G.lengthMeasure) =
      ∑ e, ∫ x in Ioo 0 (G.length e), f (G.edgePointClamped e x) := by
  rw [lengthMeasure, integral_finsetSum_measure (fun e _ => hf.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace f))]
  exact Finset.sum_congr rfl (fun e _ => G.edgeLengthMeasure_integral e f hf.measurable)

end TimeTraps.Graph
