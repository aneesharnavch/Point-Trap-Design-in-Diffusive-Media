module

public import TimeTraps.Probability.GraphBorelResolventContinuity
public import TimeTraps.Probability.MartingaleExponentialUnweight
public import TimeTraps.Probability.ExponentialResolventAlgebra

@[expose] public section

/-! The actual undiscounted resolvent martingale for bounded Borel graph
forcing, including sources with unequal traces at the vertices. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.borelResolvent_martingaleOne
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ z, ‖f z‖ ≤ C) :
    Martingale (fun (t : ℝ≥0) (p : GraphContinuousPath P.geometry) => P.borelResolventOne f (p t) -
      (∫ s in (0 : ℝ)..(t : ℝ), P.borelResolventOne f (p s.toNNReal)) +
      (∫ s in (0 : ℝ)..(t : ℝ), f (p s.toNNReal)))
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  have hr := P.borelResolventOne_continuous hf hC
  apply martingale_exponential_unweight (P.borelDiscountedResolventOne_martingale hκ x f hf hC0 hC)
    (Eventually.of_forall (P.borelDiscountedResolventOne_continuous f hf hC))
  · intro t
    have hcur := (hr.measurable.comp (graphContinuousPath_current_measurable P.geometry t)).stronglyMeasurable
    have hu := P.borelDiscountedPast_stronglyAdapted (P.borelResolventOne f) hr.measurable 0 t
    have hh := P.borelDiscountedPast_stronglyAdapted f hf 0 t
    change StronglyMeasurable[graphContinuousNaturalFiltration P.geometry t] (fun p : GraphContinuousPath P.geometry =>
      ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-(0 : ℝ) * s) * P.borelResolventOne f (p s.toNNReal)) at hu
    change StronglyMeasurable[graphContinuousNaturalFiltration P.geometry t] (fun p : GraphContinuousPath P.geometry =>
      ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-(0 : ℝ) * s) * f (p s.toNNReal)) at hh
    simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at hu hh
    convert! (hcur.sub hu).add hh using 1
  · intro t
    apply Eventually.of_forall
    intro p
    have hu : IntervalIntegrable (fun s => P.borelResolventOne f (p s.toNNReal)) volume 0 (t : ℝ) :=
      ((hr.comp p.continuous).comp continuous_real_toNNReal).intervalIntegrable _ _
    have he := exponentialResolvent_unweight_nnreal (fun r => f (p r))
      (fun r => P.borelResolventOne f (p r)) t (P.borel_path_intervalIntegrable f hf hC p 0 (t : ℝ)) hu
    simpa only [borelDiscountedResolventOne, borelDiscountedPast, neg_mul, one_mul] using he.symm

end TimeTraps.Analysis
