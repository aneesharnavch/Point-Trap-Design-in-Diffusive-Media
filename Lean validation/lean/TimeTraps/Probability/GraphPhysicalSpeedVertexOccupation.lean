module

public import TimeTraps.Probability.GraphPhysicalSpeedVertexMeasure
public import TimeTraps.Probability.GraphConservativeContinuousMarginal

@[expose] public section

/-! The actual conservative graph path spends zero ordinary time at
vertices. A single Fubini event covers the entire positive time axis,
so all finite horizons follow without substituting random times. -/

namespace TimeTraps.Analysis

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

theorem GraphShiftedContactOperatorProblem.realizedTransition_vertices
    (P : GraphShiftedContactOperatorProblem V E) (t : ℝ≥0) (ht : 0 < t)
    (x : GraphRealization P.geometry) : P.realizedTransition t x (range P.geometry.vertexPoint) = 0 := by
  rw [P.realizedTransition_pos t ht, P.realizedHeatTransition_apply]
  exact withDensity_absolutelyContinuous _ _ P.geometry.lengthMeasure_vertices

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_not_vertex
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, p t ∉ range P.geometry.vertexPoint := by
  have h : ∀ᵐ y ∂P.realizedTransition t x, y ∉ range P.geometry.vertexPoint :=
    measure_eq_zero_iff_ae_notMem.mp (P.realizedTransition_vertices t ht x)
  rw [← P.continuousPathLaw_marginal hκ x t] at h
  exact ae_of_ae_map (continuous_eval_const t).measurable.aemeasurable h

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_vertex_time_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      p r.toNNReal ∉ range P.geometry.vertexPoint := by
  let inst := P.continuousPathLaw_probability hκ x
  have hS : MeasurableSet (range P.geometry.vertexPoint) := (Set.finite_range _).measurableSet
  have he : Measurable (fun q : ℝ × GraphContinuousPath P.geometry => q.2 q.1.toNNReal) :=
    (continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp continuous_fst))).measurable
  apply (Measure.ae_ae_comm (hS.preimage he).compl).mp
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  exact P.continuousPathLaw_not_vertex hκ x r.toNNReal (Real.toNNReal_pos.mpr hr)

theorem GraphShiftedContactOperatorProblem.continuousPathLaw_zero_vertex_occupation
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ T : ℝ≥0,
      (volume.restrict (Ioc (0 : ℝ) T.val)) {r : ℝ | p r.toNNReal ∈ range P.geometry.vertexPoint} = 0 := by
  filter_upwards [P.continuousPathLaw_vertex_time_ae hκ x] with p hp
  intro T
  exact measure_eq_zero_iff_ae_notMem.mpr
    (ae_restrict_of_ae_restrict_of_subset (fun r hr => hr.1) hp)

end TimeTraps.Analysis
