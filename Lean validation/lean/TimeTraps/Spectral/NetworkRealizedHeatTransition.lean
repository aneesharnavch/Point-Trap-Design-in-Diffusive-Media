module

public import TimeTraps.Graph.RealizationLengthMeasure
public import TimeTraps.Spectral.NetworkRealizedHeatKernel
public import TimeTraps.Spectral.NetworkHeatEdgeKernelIntegral

@[expose] public section

/-! The positive-time subprobability transition on the actual compact graph.
Its density is the original heat kernel against physical edge length. -/

namespace TimeTraps.Spectral

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis TimeTraps.Graph
open scoped NNReal ENNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

noncomputable def SpectralNetwork.realizedHeatTransition (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) : Kernel (GraphRealization P.geometry) (GraphRealization P.geometry) :=
  (Kernel.const _ P.geometry.lengthMeasure).withDensity
    (fun x y => ENNReal.ofReal (P.realizedHeatKernel t ht x y))

theorem SpectralNetwork.realizedHeatTransition_apply (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (x : GraphRealization P.geometry) :
    P.realizedHeatTransition t ht x = P.geometry.lengthMeasure.withDensity
      (fun y => ENNReal.ofReal (P.realizedHeatKernel t ht x y)) :=
  Kernel.withDensity_apply _ (P.realizedHeatKernel_measurable t ht).ennreal_ofReal x

theorem SpectralNetwork.realizedHeatKernel_clamped (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e d : E) (x : Icc (0 : ℝ) (P.length e)) (y : ℝ) :
    P.realizedHeatKernel t ht (P.geometry.edgePoint e x) (P.geometry.edgePointClamped d y) =
      P.heatKernelClamped t ht e d x y :=
  P.realizedHeatKernel_edge t ht e d x _

theorem SpectralNetwork.realizedHeatTransition_mass_edge (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (e : E) (x : Icc (0 : ℝ) (P.length e)) :
    P.realizedHeatTransition t ht (P.geometry.edgePoint e x) univ =
      ∑ d, P.heatEdgeKernel t ht e d x univ := by
  rw [P.realizedHeatTransition_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, P.geometry.lengthMeasure_lintegral _
      ((P.realizedHeatKernel_measurable t ht).of_uncurry_left.ennreal_ofReal)]
  apply Finset.sum_congr rfl
  intro d _
  rw [P.heatEdgeKernel_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  apply lintegral_congr
  intro y
  rw [P.realizedHeatKernel_clamped t ht e d x y]

theorem SpectralNetwork.realizedHeatTransition_mass (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (x : GraphRealization P.geometry) :
    P.realizedHeatTransition t ht x univ =
      ENNReal.ofReal (P.realizedHeatEvaluation t ht x
        (graphSobolevSpaceStateL P.geometry P.operatorOne)) := by
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  rw [P.realizedHeatTransition_mass_edge t ht e u,
    P.realizedHeatEvaluation_edge t ht e u]
  exact P.heatEdgeKernel_sum_mass t ht e u

theorem SpectralNetwork.realizedHeatTransition_mass_le_one (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (x : GraphRealization P.geometry) :
    P.realizedHeatTransition t ht x univ ≤ 1 := by
  obtain ⟨e, u, rfl⟩ := P.geometry.edgePoint_surjective x
  rw [P.realizedHeatTransition_mass_edge t ht e u]
  exact P.heatEdgeKernel_sum_mass_le_one t ht e u

instance SpectralNetwork.realizedHeatTransition_finite (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) : IsFiniteKernel (P.realizedHeatTransition t ht) where
  exists_univ_le := ⟨1, ENNReal.one_lt_top, P.realizedHeatTransition_mass_le_one t ht⟩

theorem SpectralNetwork.realizedHeatTransition_integral (P : SpectralNetwork V E)
    (t : ℝ≥0) (ht : 0 < t) (x : GraphRealization P.geometry)
    (f : GraphRealization P.geometry → ℝ) :
    (∫ y, f y ∂P.realizedHeatTransition t ht x) =
      ∫ y, P.realizedHeatKernel t ht x y * f y ∂P.geometry.lengthMeasure := by
  rw [P.realizedHeatTransition_apply,
    integral_withDensity_eq_integral_toReal_smul
      (P.realizedHeatKernel_measurable t ht).of_uncurry_left.ennreal_ofReal
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun y => by
    change (ENNReal.ofReal (P.realizedHeatKernel t ht x y)).toReal * f y = _
    rw [ENNReal.toReal_ofReal (P.realizedHeatKernel_nonneg t ht x y)]
    )

end TimeTraps.Spectral
