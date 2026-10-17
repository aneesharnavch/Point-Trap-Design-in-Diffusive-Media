module

public import TimeTraps.Analysis.GraphConservativeCoordinateFourthNorm

@[expose] public section

/-! Genuine vector fourth-moment integrability and bounds follow from
the finitely many scalar coordinate moments. The integral is over the
original measure and uses the actual product/sup norm. -/

namespace TimeTraps.Graph

open MeasureTheory TimeTraps.Analysis

variable {V E Ω : Type*} [Fintype V] [Fintype E] [MeasurableSpace Ω]

theorem graphCoordinateProjection_fourth_integrable (μ : Measure Ω)
    (X Y : Ω → GraphRealizationCoordinates V E)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)
    (hφ : ∀ i : GraphCoordinateIndex V E, Integrable
      (fun ω => (graphCoordinateProjection i (X ω) - graphCoordinateProjection i (Y ω)) ^ 4) μ) :
    Integrable (fun ω => ‖X ω - Y ω‖ ^ 4) μ := by
  have hi := integrable_finsetSum Finset.univ (fun i _ => hφ i)
  apply hi.mono' ((hX.sub hY).norm.pow 4)
  exact Filter.Eventually.of_forall fun ω => by
    change ‖‖X ω - Y ω‖ ^ 4‖ ≤ _
    simpa only [norm_pow, norm_norm] using graphCoordinateProjection_sub_fourth_le_sum (X ω) (Y ω)

theorem graphCoordinateProjection_fourth_integral_le_sum (μ : Measure Ω)
    (X Y : Ω → GraphRealizationCoordinates V E)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)
    (hφ : ∀ i : GraphCoordinateIndex V E, Integrable
      (fun ω => (graphCoordinateProjection i (X ω) - graphCoordinateProjection i (Y ω)) ^ 4) μ) :
    (∫ ω, ‖X ω - Y ω‖ ^ 4 ∂μ) ≤
      ∑ i : GraphCoordinateIndex V E,
        ∫ ω, (graphCoordinateProjection i (X ω) - graphCoordinateProjection i (Y ω)) ^ 4 ∂μ := by
  have hi := graphCoordinateProjection_fourth_integrable μ X Y hX hY hφ
  have hs := integrable_finsetSum Finset.univ (fun i _ => hφ i)
  calc
    _ ≤ ∫ ω, ∑ i : GraphCoordinateIndex V E,
        (graphCoordinateProjection i (X ω) - graphCoordinateProjection i (Y ω)) ^ 4 ∂μ :=
      integral_mono hi hs (fun ω => graphCoordinateProjection_sub_fourth_le_sum (X ω) (Y ω))
    _ = _ := integral_finsetSum Finset.univ (fun i _ => hφ i)

theorem graphCoordinateProjection_fourth_integral_bound (μ : Measure Ω)
    (X Y : Ω → GraphRealizationCoordinates V E)
    (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ)
    (hφ : ∀ i : GraphCoordinateIndex V E, Integrable
      (fun ω => (graphCoordinateProjection i (X ω) - graphCoordinateProjection i (Y ω)) ^ 4) μ)
    (C : GraphCoordinateIndex V E → ℝ) (r : ℝ)
    (hC : ∀ i, (∫ ω,
      (graphCoordinateProjection i (X ω) - graphCoordinateProjection i (Y ω)) ^ 4 ∂μ) ≤ C i * r) :
    (∫ ω, ‖X ω - Y ω‖ ^ 4 ∂μ) ≤ (∑ i, C i) * r := by
  calc
    _ ≤ ∑ i : GraphCoordinateIndex V E,
        ∫ ω, (graphCoordinateProjection i (X ω) - graphCoordinateProjection i (Y ω)) ^ 4 ∂μ :=
      graphCoordinateProjection_fourth_integral_le_sum μ X Y hX hY hφ
    _ ≤ ∑ i, C i * r := Finset.sum_le_sum (fun i _ => hC i)
    _ = _ := (Finset.sum_mul Finset.univ C r).symm

end TimeTraps.Graph
