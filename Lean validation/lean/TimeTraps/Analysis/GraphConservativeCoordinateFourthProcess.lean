module

public import TimeTraps.Analysis.GraphConservativeCoordinateFourthIntegral

@[expose] public section

/-! Finitely many uniform scalar increment estimates yield one uniform
fourth-moment estimate for the genuine graph-coordinate vector process.
Only the supplied measure and literal process observations occur here. -/

namespace TimeTraps.Graph

open MeasureTheory TimeTraps.Analysis

variable {V E Ω T : Type*} [Fintype V] [Fintype E] [MeasurableSpace Ω]

theorem graphCoordinateProjection_process_fourth_bound (μ : Measure Ω)
    (X : T → Ω → GraphRealizationCoordinates V E) (d : T → T → ℝ)
    (hX : ∀ t, AEStronglyMeasurable (X t) μ)
    (hφ : ∀ i : GraphCoordinateIndex V E, ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
      Integrable (fun ω =>
        (graphCoordinateProjection i (X s ω) - graphCoordinateProjection i (X t ω)) ^ 4) μ ∧
      (∫ ω, (graphCoordinateProjection i (X s ω) - graphCoordinateProjection i (X t ω)) ^ 4 ∂μ)
        ≤ C * (d s t) ^ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s t,
      Integrable (fun ω => ‖X s ω - X t ω‖ ^ 4) μ ∧
      (∫ ω, ‖X s ω - X t ω‖ ^ 4 ∂μ) ≤ C * (d s t) ^ 2 := by
  classical
  choose C hC using hφ
  refine ⟨∑ i, C i, Finset.sum_nonneg (fun i _ => (hC i).1), ?_⟩
  intro s t
  have hi : ∀ i : GraphCoordinateIndex V E, Integrable (fun ω =>
      (graphCoordinateProjection i (X s ω) - graphCoordinateProjection i (X t ω)) ^ 4) μ :=
    fun i => ((hC i).2 s t).1
  refine ⟨graphCoordinateProjection_fourth_integrable μ (X s) (X t) (hX s) (hX t) hi, ?_⟩
  exact graphCoordinateProjection_fourth_integral_bound μ (X s) (X t) (hX s) (hX t) hi
    C ((d s t) ^ 2) (fun i => ((hC i).2 s t).2)

end TimeTraps.Graph
