module

public import TimeTraps.Probability.GraphAtomicHazardMeasure

@[expose] public section

/-! Literal weighted contact cancellation for the actual graph hazard.
The spatial factor is arbitrary, since each local-time measure is
supported on visits to its target. All vertices are included. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability
open scoped NNReal ENNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

theorem GraphShiftedContactOperatorProblem.atomicHazardStieltjes_weighted_contact
    (P : GraphShiftedContactOperatorProblem V E) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (p : GraphContinuousPath P.geometry)
    (w : ℝ≥0 → ℝ) (hw : Continuous w) (g : GraphRealization P.geometry → ℝ) (T : ℝ≥0) :
    IntegrableOn (fun r => w r.toNNReal * g (p r.toNNReal)) (Ioc (0 : ℝ) (T : ℝ))
      (P.atomicHazardStieltjes a κ hκ p).measure ∧
    (∫ r in Ioc (0 : ℝ) (T : ℝ), w r.toNNReal * g (p r.toNNReal)
      ∂(P.atomicHazardStieltjes a κ hκ p).measure) =
      ∑ i, κ i * g (a i) * ∫ r in Ioc (0 : ℝ) (T : ℝ), w r.toNNReal ∂P.pointLocalTimeMeasure (a i) p := by
  let μ : I → Measure ℝ := fun i => P.pointLocalTimeMeasure (a i) p
  let f : ℝ → ℝ := fun r => w r.toNNReal * g (p r.toNNReal)
  have hi (i : I) := P.pointLocalTimeMeasure_weighted_contact (a i) p w hw g T
  have hr : ((P.atomicHazardStieltjes a κ hκ p).measure).restrict (Ioc (0 : ℝ) (T : ℝ)) =
      ∑ i, Real.toNNReal (κ i) • (μ i).restrict (Ioc (0 : ℝ) (T : ℝ)) := by
    rw [P.atomicHazardStieltjes_measure_sum]
    change (Measure.restrictₗ (Ioc (0 : ℝ) (T : ℝ))) (∑ i, Real.toNNReal (κ i) • μ i) = _
    rw [map_sum]
    exact Finset.sum_congr rfl (fun i _ => Measure.restrict_smul _ _ _)
  have hfi (i : I) : Integrable f (Real.toNNReal (κ i) • (μ i).restrict (Ioc (0 : ℝ) (T : ℝ))) :=
    (hi i).1.smul_measure_nnreal
  constructor
  · change Integrable f _
    rw [hr]
    exact integrable_finsetSum_measure.mpr (fun i _ => hfi i)
  · change (∫ r, f r ∂((P.atomicHazardStieltjes a κ hκ p).measure).restrict (Ioc (0 : ℝ) (T : ℝ))) = _
    rw [hr, integral_finsetSum_measure (fun i _ => hfi i)]
    apply Finset.sum_congr rfl
    intro i _
    rw [integral_smul_nnreal_measure]
    change (Real.toNNReal (κ i) : ℝ) * (∫ r in Ioc (0 : ℝ) (T : ℝ), f r ∂μ i) = _
    rw [Real.coe_toNNReal _ (hκ i)]
    have he : (∫ r in Ioc (0 : ℝ) (T : ℝ), f r ∂μ i) =
        g (a i) * ∫ r in Ioc (0 : ℝ) (T : ℝ), w r.toNNReal ∂μ i := (hi i).2
    rw [he]
    ring

end TimeTraps.Analysis
