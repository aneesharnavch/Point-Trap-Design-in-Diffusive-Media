module

public import TimeTraps.Probability.GraphPointLocalTimeDiscountResolvent
public import TimeTraps.Probability.GraphPointLocalTimeDiscountParts
public import TimeTraps.Probability.GraphPointLocalTimeContactMeasure
public import TimeTraps.Analysis.GraphHeatPointResolventRegularity

@[expose] public section

/-! The discounted prefix is the genuine Stieltjes local-time integral.
The raw-adapted and canonical contact formulas agree at every time on
one event. Spatial continuity of the proved resolvent supplies continuous
paths for the actual martingale. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscount_contact_parts
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (p : GraphContinuousPath P.geometry) {α : ℝ} (hα : 0 ≤ α) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) (T : ℝ), Real.exp (-(α * r)) ∂P.pointLocalTimeMeasure a p) =
      Real.exp (-(α * (T : ℝ))) * P.pointLocalTimePath a p T +
        α * ∫ r in (0 : ℝ)..(T : ℝ), Real.exp (-(α * r)) * P.pointLocalTimePath a p r.toNNReal := by
  have hc : Continuous (P.pointLocalTimeStieltjes a p) :=
    (P.pointLocalTimePath a p).continuous.comp continuous_real_toNNReal
  have h := graphPointDiscount_stieltjes_parts (P.pointLocalTimeStieltjes a p) hc hα T
  change (∫ r in Ioc (0 : ℝ) (T : ℝ), Real.exp (-(α * r)) ∂P.pointLocalTimeMeasure a p) =
      Real.exp (-(α * (T : ℝ))) * P.pointLocalTimePath a p (T : ℝ).toNNReal - P.pointLocalTimePath a p (0 : ℝ).toNNReal +
        α * ∫ r in (0 : ℝ)..(T : ℝ), Real.exp (-(α * r)) * P.pointLocalTimePath a p r.toNNReal at h
  simpa only [Real.toNNReal_coe, Real.toNNReal_zero, P.pointLocalTimePath_zero, sub_zero] using h

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPrefix_contact_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 ≤ α) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ T : ℝ≥0,
      P.pointLocalTimeDiscountedPrefix a α T p =
        ∫ r in Ioc (0 : ℝ) (T : ℝ), Real.exp (-(α * r)) ∂P.pointLocalTimeMeasure a p := by
  filter_upwards [P.pointLocalTime_eq_path_ae hκ x a] with p hp T
  rw [P.pointLocalTimeDiscount_contact_parts a p hα T]
  simp only [pointLocalTimeDiscountedPrefix, hp]

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedResolvent_contact_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 ≤ α) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, ∀ T : ℝ≥0,
      P.pointLocalTimeDiscountedResolvent a α T p =
        (∫ r in Ioc (0 : ℝ) (T : ℝ), Real.exp (-(α * r)) ∂P.pointLocalTimeMeasure a p) +
          Real.exp (-(α * (T : ℝ))) * P.pointLocalTimeDiscountedPotential a α (p T) := by
  filter_upwards [P.pointLocalTimeDiscountedPrefix_contact_ae hκ x a hα] with p hp T
  exact congrArg (fun z => z + Real.exp (-(α * (T : ℝ))) * P.pointLocalTimeDiscountedPotential a α (p T)) (hp T)

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedResolvent_continuous_ae
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) {α : ℝ} (hα : 0 < α) :
    ∀ᵐ p ∂P.continuousPathLaw hκ x, Continuous (fun t => P.pointLocalTimeDiscountedResolvent a α t p) := by
  filter_upwards [P.pointLocalTime_regular_ae hκ x a] with p hp
  have hw : Continuous (fun r : ℝ => Real.exp (-(α * r))) := by fun_prop
  have hl : Continuous (fun r : ℝ => Real.exp (-(α * r)) * P.pointLocalTime a r.toNNReal p) :=
    hw.mul (hp.1.comp continuous_real_toNNReal)
  have hi : Continuous (fun r : ℝ => ∫ s in (0 : ℝ)..r, Real.exp (-(α * s)) * P.pointLocalTime a s.toNNReal p) :=
    continuous_iff_continuousAt.mpr (fun r => (hl.integral_hasStrictDerivAt 0 r).hasDerivAt.continuousAt)
  have hR := (P.pointLocalTimeDiscountedPotential_continuous hα).comp
    (show Continuous (fun t : ℝ≥0 => (p t, a)) from p.continuous.prodMk continuous_const)
  exact (((hw.comp NNReal.continuous_coe).mul hp.1).add
    ((hi.comp NNReal.continuous_coe).const_mul α)).add ((hw.comp NNReal.continuous_coe).mul hR)

end TimeTraps.Analysis
