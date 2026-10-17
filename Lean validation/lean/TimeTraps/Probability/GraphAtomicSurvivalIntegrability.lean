module

public import TimeTraps.Probability.GraphAtomicCompensatedExpectation

@[expose] public section

/-! Actual graph survival has jointly Borel values, integrable bounded
observations, and nonincreasing paths on one event for all times. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter TimeTraps.Graph TimeTraps.Probability
open scoped NNReal

variable {V E I : Type*} [Fintype V] [Fintype E] [Nonempty E] [Fintype I]

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.atomicSurvival_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) :
    Measurable (fun q : ℝ × GraphContinuousPath P.geometry => P.atomicSurvival a κ q.1.toNNReal q.2) := by
  have hm : Measurable (fun q : ℝ × GraphContinuousPath P.geometry => ((q.1.toNNReal : ℝ), q.2)) :=
    measurable_fst.real_toNNReal.coe_nnreal_real.prodMk measurable_snd
  exact ((P.atomicKillingClock_jointlyMeasurable a κ).comp hm).neg.exp

theorem GraphShiftedContactOperatorProblem.atomicSurvival_antitone_ae
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) :
    ∀ᵐ p ∂P.continuousPathLaw h0 x, Antitone (fun t => P.atomicSurvival a κ t p) := by
  filter_upwards [P.atomicKillingClock_paths_ae h0 x a κ hκ] with p hp
  intro s t hst
  exact Real.exp_le_exp.mpr (neg_le_neg (hp.2 s.coe_nonneg t.coe_nonneg hst))

theorem GraphShiftedContactOperatorProblem.atomicSurvival_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    Integrable (P.atomicSurvival a κ T) (P.continuousPathLaw h0 x) := by
  let _ := P.continuousPathLaw_probability h0 x
  apply (integrable_const (1 : ℝ)).mono'
    (((P.atomicSurvival_stronglyAdapted a κ) T).mono
      ((graphContinuousNaturalFiltration P.geometry).le T)).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_pos (P.atomicSurvival_bounds a κ hκ T p).1]
  exact (P.atomicSurvival_bounds a κ hκ T p).2

theorem GraphShiftedContactOperatorProblem.atomicSurvival_observation_integrable
    (P : GraphShiftedContactOperatorProblem V E) (h0 : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (a : I → GraphRealization P.geometry)
    (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i) (u : C(GraphRealization P.geometry, ℝ)) (T : ℝ≥0) :
    Integrable (fun p => P.atomicSurvival a κ T p * u (p T)) (P.continuousPathLaw h0 x) := by
  let _ := P.continuousPathLaw_probability h0 x
  have hu : Integrable (fun p : GraphContinuousPath P.geometry => u (p T)) (P.continuousPathLaw h0 x) := by
    apply (integrable_const ‖u‖).mono'
      (u.continuous.comp (continuous_eval_const T)).measurable.aestronglyMeasurable
    exact Eventually.of_forall (fun p => u.norm_coe_le_norm (p T))
  apply hu.bdd_mul (((P.atomicSurvival_stronglyAdapted a κ) T).mono
    ((graphContinuousNaturalFiltration P.geometry).le T)).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  rw [Real.norm_eq_abs, abs_of_pos (P.atomicSurvival_bounds a κ hκ T p).1]
  exact (P.atomicSurvival_bounds a κ hκ T p).2

theorem GraphShiftedContactOperatorProblem.atomicRunningCost_jointlyMeasurable
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) :
    Measurable (fun q : ℝ × GraphContinuousPath P.geometry =>
      P.atomicSurvival a κ q.1.toNNReal q.2 * P.geometry.physicalSpeed b (q.2 q.1.toNNReal)) := by
  have he : Measurable (fun q : ℝ × GraphContinuousPath P.geometry => q.2 q.1.toNNReal) :=
    (continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp continuous_fst))).measurable
  exact (P.atomicSurvival_jointlyMeasurable a κ).mul ((P.geometry.physicalSpeed_measurable b).comp he)

theorem GraphShiftedContactOperatorProblem.atomicRunningCost_path_integrable
    (P : GraphShiftedContactOperatorProblem V E) (b : ℝ) (hb : 0 < b)
    (a : I → GraphRealization P.geometry) (κ : I → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (T : ℝ≥0) (p : GraphContinuousPath P.geometry) :
    IntegrableOn (fun r : ℝ => P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal))
      (Ioc 0 (T : ℝ)) := by
  have hp : Measurable (fun r : ℝ => (r, p)) := measurable_id.prodMk measurable_const
  have hm0 := (P.atomicRunningCost_jointlyMeasurable b a κ).comp hp
  have he : ((fun q : ℝ × GraphContinuousPath P.geometry =>
      P.atomicSurvival a κ q.1.toNNReal q.2 * P.geometry.physicalSpeed b (q.2 q.1.toNNReal)) ∘ fun r : ℝ => (r, p)) =
      (fun r : ℝ => P.atomicSurvival a κ r.toNNReal p * P.geometry.physicalSpeed b (p r.toNNReal)) := rfl
  rw [he] at hm0
  have hm := hm0
  have hc : IntegrableOn (fun _r : ℝ => (P.geometry.physicalSpeedUpper b hb : ℝ)) (Ioc 0 (T : ℝ)) :=
    integrableOn_const (hs := by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
  refine hc.mono' hm.aestronglyMeasurable ?_
  apply Eventually.of_forall
  intro r
  have hH := P.atomicSurvival_bounds a κ hκ r.toNNReal p
  have hρ := P.geometry.physicalSpeed_bound b hb (p r.toNNReal)
  have hρ0 : 0 ≤ P.geometry.physicalSpeed b (p r.toNNReal) := le_trans (NNReal.coe_nonneg _) hρ.1
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hH.1.le hρ0)]
  exact (mul_le_of_le_one_left hρ0 hH.2).trans hρ.2

end TimeTraps.Analysis
