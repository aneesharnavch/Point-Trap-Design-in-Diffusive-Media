module

public import TimeTraps.Probability.GraphPointLocalTimeDiscountContact
public import TimeTraps.Probability.GraphBorelResolventPast
public import TimeTraps.Probability.MartingaleExponentialUnweight
public import TimeTraps.Probability.ExponentialResolventAlgebra

@[expose] public section

/-! The actual undiscounted point-source resolvent martingale at every
point of the original graph, including vertices. The sign agrees with
(1-L)r=delta: r(Xt)-integral(r(Xs))+ell(t). -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph TimeTraps.Probability Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.pointLocalTimeResolvent_martingaleOne
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x a : GraphRealization P.geometry) :
    Martingale (fun (t : ℝ≥0) (p : GraphContinuousPath P.geometry) => P.pointLocalTimeDiscountedPotential a 1 (p t) -
      (∫ s in (0 : ℝ)..(t : ℝ), P.pointLocalTimeDiscountedPotential a 1 (p s.toNNReal)) +
      P.pointLocalTime a t p)
      (graphContinuousNaturalFiltration P.geometry) (P.continuousPathLaw hκ x) := by
  let inst := P.continuousPathLaw_probability hκ x
  have hparam : Continuous (fun y : GraphRealization P.geometry => (y, a)) :=
    continuous_id.prodMk continuous_const
  have hRjoint := P.pointLocalTimeDiscountedPotential_continuous (q := 1) (by norm_num)
  have hr := hRjoint.comp hparam
  apply martingale_exponential_unweight (P.pointLocalTimeDiscountedResolvent_martingale hκ x a (α := 1) (by norm_num))
    (P.pointLocalTimeDiscountedResolvent_continuous_ae hκ x a (α := 1) (by norm_num))
  · intro t
    have hcur := (hr.measurable.comp (graphContinuousPath_current_measurable P.geometry t)).stronglyMeasurable
    have hu := P.borelDiscountedPast_stronglyAdapted (P.pointLocalTimeDiscountedPotential a 1) hr.measurable 0 t
    change StronglyMeasurable[graphContinuousNaturalFiltration P.geometry t] (fun p : GraphContinuousPath P.geometry =>
      ∫ s in (0 : ℝ)..(t : ℝ), Real.exp (-(0 : ℝ) * s) * P.pointLocalTimeDiscountedPotential a 1 (p s.toNNReal)) at hu
    simp only [neg_zero, zero_mul, Real.exp_zero, one_mul] at hu
    convert! (hcur.sub hu).add (P.pointLocalTime_stronglyAdapted a t) using 1
  · intro t
    filter_upwards [P.pointLocalTime_regular_ae hκ x a] with p hp
    let A : ℝ≥0 → ℝ := fun r => P.pointLocalTime a r p
    let R : ℝ≥0 → ℝ := fun r => P.pointLocalTimeDiscountedPotential a 1 (p r)
    have hA : IntervalIntegrable (fun r => A r.toNNReal) volume 0 (t : ℝ) :=
      (hp.1.comp continuous_real_toNNReal).intervalIntegrable _ _
    have hR : IntervalIntegrable (fun r => R r.toNNReal) volume 0 (t : ℝ) :=
      ((hr.comp p.continuous).comp continuous_real_toNNReal).intervalIntegrable _ _
    have he := exponentialResolvent_unweight_nnreal A (fun r => A r + R r) t hA (hA.add hR)
    rw [intervalIntegral.integral_add hA hR] at he
    have hm (r : ℝ≥0) : P.pointLocalTimeDiscountedResolvent a 1 r p =
        (∫ s in (0 : ℝ)..(r : ℝ), Real.exp (-s) * A s.toNNReal) +
          Real.exp (-(r : ℝ)) * (A r + R r) := by
      simp only [pointLocalTimeDiscountedResolvent, pointLocalTimeDiscountedPrefix, one_mul, A, R]
      ring
    simp_rw [hm]
    change R t - (∫ s in (0 : ℝ)..(t : ℝ), R s.toNNReal) + A t = _
    rw [he]
    ring

end TimeTraps.Analysis
