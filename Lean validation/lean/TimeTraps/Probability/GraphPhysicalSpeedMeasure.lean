module

public import TimeTraps.Probability.GraphPhysicalSpeedBounds
public import TimeTraps.Probability.GraphPhysicalSpeedVertexMeasure
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

@[expose] public section

/-! The original physical speed measure on the compact graph. The fixed
vertex value one only chooses a Borel representative: every other vertex
value gives exactly the same measure because vertices have zero length. -/

namespace TimeTraps.Graph

open Set MeasureTheory Filter
open scoped ENNReal NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem MetricGraph.physicalSpeed_eq_ae (G : MetricGraph V E) (b c : ℝ) :
    G.physicalSpeed b =ᵐ[G.lengthMeasure] G.physicalSpeed c := by
  have hn : ∀ᵐ p ∂G.lengthMeasure, p ∉ range G.vertexPoint := by
    rw [ae_iff]
    have he : {p | ¬p ∉ range G.vertexPoint} = range G.vertexPoint := by
      ext p
      simp only [mem_ofPred_eq, not_not]
    rw [he]
    exact G.lengthMeasure_vertices
  filter_upwards [hn] with p hp
  rcases G.point_vertex_or_openEdge p with ⟨v, rfl⟩ | ⟨e, y, rfl⟩
  · exact (hp ⟨v, rfl⟩).elim
  · rw [G.physicalSpeed_openEdge, G.physicalSpeed_openEdge]

noncomputable def MetricGraph.physicalSpeedMeasure (G : MetricGraph V E) :
    Measure (GraphRealization G) :=
  G.lengthMeasure.withDensity (fun p => ENNReal.ofReal (G.physicalSpeed 1 p))

theorem MetricGraph.physicalSpeedMeasure_eq_withDensity (G : MetricGraph V E) (b : ℝ) :
    G.physicalSpeedMeasure =
      G.lengthMeasure.withDensity (fun p => ENNReal.ofReal (G.physicalSpeed b p)) :=
  withDensity_congr_ae ((G.physicalSpeed_eq_ae 1 b).fun_comp ENNReal.ofReal)

instance graphPhysicalSpeedMeasure_finite (G : MetricGraph V E) :
    IsFiniteMeasure G.physicalSpeedMeasure := by
  have hpos (p) : 0 ≤ G.physicalSpeed 1 p :=
    (G.physicalSpeedLower 1 zero_lt_one).coe_nonneg.trans (G.physicalSpeed_bound 1 zero_lt_one p).1
  have hi : Integrable (G.physicalSpeed 1) G.lengthMeasure := by
    apply (integrable_const (G.physicalSpeedUpper 1 zero_lt_one : ℝ)).mono'
      (G.physicalSpeed_measurable 1).aestronglyMeasurable
    exact Eventually.of_forall (fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hpos p)]
      exact (G.physicalSpeed_bound 1 zero_lt_one p).2)
  exact isFiniteMeasure_withDensity
    ((hasFiniteIntegral_iff_ofReal (Eventually.of_forall hpos)).mp hi.hasFiniteIntegral).ne

theorem MetricGraph.physicalSpeedMeasure_integral (G : MetricGraph V E)
    (b : ℝ) (hb : 0 < b) (f : GraphRealization G → ℝ) :
    (∫ p, f p ∂G.physicalSpeedMeasure) =
      ∫ p, G.physicalSpeed b p * f p ∂G.lengthMeasure := by
  rw [G.physicalSpeedMeasure_eq_withDensity b,
    integral_withDensity_eq_integral_toReal_smul (G.physicalSpeed_measurable b).ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun p => by
    dsimp only
    rw [ENNReal.toReal_ofReal
      ((G.physicalSpeedLower b hb).coe_nonneg.trans (G.physicalSpeed_bound b hb p).1), smul_eq_mul])

theorem MetricGraph.physicalSpeedMeasure_integrable_iff (G : MetricGraph V E)
    (b : ℝ) (hb : 0 < b) (f : GraphRealization G → ℝ) :
    Integrable f G.physicalSpeedMeasure ↔
      Integrable (fun p => G.physicalSpeed b p * f p) G.lengthMeasure := by
  rw [G.physicalSpeedMeasure_eq_withDensity b,
    integrable_withDensity_iff_integrable_smul' (G.physicalSpeed_measurable b).ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  have he : (fun p => (ENNReal.ofReal (G.physicalSpeed b p)).toReal • f p) =
      (fun p => G.physicalSpeed b p * f p) := by
    funext p
    rw [ENNReal.toReal_ofReal
      ((G.physicalSpeedLower b hb).coe_nonneg.trans (G.physicalSpeed_bound b hb p).1), smul_eq_mul]
  rw [he]

end TimeTraps.Graph
