module

public import TimeTraps.Probability.GraphPointLocalTimeDiscountDecomposition

@[expose] public section

/-! The explicit discounted local-time resolvent process is a martingale
in the raw natural filtration. Its prefix uses only observations up to
the current time, including on exceptional paths. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPrefix_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (α : ℝ) :
    StronglyAdapted (graphContinuousNaturalFiltration P.geometry) (P.pointLocalTimeDiscountedPrefix a α) := by
  intro t
  have hi : StronglyMeasurable[graphContinuousNaturalFiltration P.geometry t]
      (fun p : GraphContinuousPath P.geometry =>
        ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-(α * s)) * P.pointLocalTime a s.toNNReal p) := by
    have he : (fun p : GraphContinuousPath P.geometry =>
        ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-(α * s)) * P.pointLocalTime a s.toNNReal p) =
        (fun p => ∫ s in Ioc (0 : ℝ) (t : ℝ),
          Real.exp (-(α * s)) * P.pointLocalTime a (min t s.toNNReal) p) := by
      funext p
      rw [intervalIntegral.integral_of_le t.coe_nonneg]
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [min_eq_right (Real.toNNReal_le_iff_le_coe.mpr hs.2)]
    rw [he]
    let : MeasurableSpace (GraphContinuousPath P.geometry) := graphContinuousNaturalFiltration P.geometry t
    have hw : StronglyMeasurable (fun q : ℝ × GraphContinuousPath P.geometry => Real.exp (-(α * q.1))) :=
      (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).stronglyMeasurable.comp_measurable measurable_fst
    exact (hw.mul (P.pointLocalTime_clamped_jointlyMeasurable a t).stronglyMeasurable).integral_prod_left'
      (μ := volume.restrict (Ioc (0 : ℝ) (t : ℝ)))
  exact ((P.pointLocalTime_stronglyAdapted a t).const_mul (Real.exp (-(α * (t : ℝ))))).add (hi.const_mul α)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedResolvent_stronglyAdapted
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry) (α : ℝ) :
    StronglyAdapted (graphContinuousNaturalFiltration P.geometry) (P.pointLocalTimeDiscountedResolvent a α) := by
  intro t
  exact (P.pointLocalTimeDiscountedPrefix_stronglyAdapted a α t).add
    (((P.pointLocalTimeDiscountedPotential_measurable a α).comp
      (graphContinuousPath_current_measurable P.geometry t)).stronglyMeasurable.const_mul (Real.exp (-(α * (t : ℝ)))))

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedResolvent_martingale
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) :
    Martingale (P.pointLocalTimeDiscountedResolvent a α) (graphContinuousNaturalFiltration P.geometry)
      (P.continuousPathLaw hκ x) :=
  (P.pointLocalTimeDiscountedTerminal_martingale hκ x a hα).congr
    (P.pointLocalTimeDiscountedResolvent_stronglyAdapted a α)
    (P.pointLocalTimeDiscountedTerminal_decomposition hκ x a hα)

end TimeTraps.Analysis
