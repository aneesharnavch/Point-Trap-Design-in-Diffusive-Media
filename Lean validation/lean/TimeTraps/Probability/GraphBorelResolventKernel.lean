module

public import TimeTraps.Probability.GraphBorelResolventLaplace
public import TimeTraps.Analysis.GraphHeatPointKernelLaplace
public import TimeTraps.Analysis.GraphHeatResolventBorel

@[expose] public section

/-! The actual bounded-Borel transition Laplace integral equals the
original graph weak resolvent. The time/source interchange is justified
by the proved integrable square-root kernel envelope. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter
open scoped NNReal

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.borelResolventKernel_product_integrable
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphRealization P.geometry)
    (f : GraphRealization P.geometry → ℝ) (hf : Measurable f) {D : ℝ} (hD : ∀ y, ‖f y‖ ≤ D) :
    Integrable (fun z : ℝ × GraphRealization P.geometry =>
      Real.exp (-z.1) * (f z.2 * P.realizedHeatPointKernelTime x z.2 z.1))
      ((volume.restrict (Ioi 0)).prod P.geometry.lengthMeasure) := by
  obtain ⟨C, _, hb⟩ := P.realizedHeatKernel_global_bound
  have hfi : Integrable f P.geometry.lengthMeasure :=
    (integrable_const D).mono' hf.aestronglyMeasurable (Eventually.of_forall hD)
  have hi := (graphPointKernelDiscount_envelope_integrable.const_mul C).mul_prod hfi.norm
  have hparam : Measurable (fun z : ℝ × GraphRealization P.geometry => (z.1, (x, z.2))) := by fun_prop
  have hk := P.realizedHeatPointKernelTime_jointlyMeasurable.comp hparam
  have he : Measurable (fun z : ℝ × GraphRealization P.geometry => Real.exp (-z.1)) := by fun_prop
  have hm := he.mul ((hf.comp measurable_snd).mul hk)
  apply hi.mono' hm.aestronglyMeasurable
  have htime : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).prod P.geometry.lengthMeasure), 0 < z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioi (0 : ℝ)))
      (ν := P.geometry.lengthMeasure)).ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [htime] with z hz
  change ‖Real.exp (-z.1) * (f z.2 * P.realizedHeatPointKernelTime x z.2 z.1)‖ ≤
    (C * (Real.exp (-z.1) * (1 + 1 / Real.sqrt z.1))) * ‖f z.2‖
  rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), norm_mul,
    Real.norm_eq_abs (P.realizedHeatPointKernelTime _ _ _),
    abs_of_nonneg (P.realizedHeatPointKernelTime_nonneg x z.2 z.1)]
  have hkbound : P.realizedHeatPointKernelTime x z.2 z.1 ≤ C * (1 + 1 / Real.sqrt z.1) := by
    unfold realizedHeatPointKernelTime
    rw [dif_pos hz]
    simpa only [Real.coe_toNNReal z.1 hz.le] using
      (hb z.1.toNNReal (Real.toNNReal_pos.mpr hz) x z.2).2
  have hh := mul_le_mul_of_nonneg_left hkbound
    (mul_nonneg (Real.exp_pos (-z.1)).le (norm_nonneg (f z.2)))
  nlinarith

theorem GraphShiftedContactOperatorProblem.borelTransitionLaplace_one_eq
    (P : GraphShiftedContactOperatorProblem V E) (x : GraphRealization P.geometry)
    (f : GraphRealization P.geometry → ℝ) (hf : Measurable f) {D : ℝ} (hD : ∀ y, ‖f y‖ ≤ D) :
    P.borelTransitionLaplace f 1 x = P.borelResolventOne f x := by
  have hi := P.borelResolventKernel_product_integrable x f hf hD
  unfold borelTransitionLaplace borelResolventOne
  simp only [neg_one_mul]
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ y, Real.exp (-t) * (f y * P.realizedHeatPointKernelTime x y t)
        ∂P.geometry.lengthMeasure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := ht
      rw [P.realizedTransition_pos t.toNNReal (Real.toNNReal_pos.mpr ht0), P.realizedHeatTransition_integral,
        ← integral_const_mul]
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      simp only [realizedHeatPointKernelTime, dif_pos ht0]
      ring
    _ = ∫ y, (∫ t in Ioi (0 : ℝ), Real.exp (-t) * (f y * P.realizedHeatPointKernelTime x y t))
        ∂P.geometry.lengthMeasure := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro y
      dsimp only
      have he : (∫ t in Ioi (0 : ℝ), Real.exp (-t) * (f y * P.realizedHeatPointKernelTime x y t)) =
          f y * ∫ t in Ioi (0 : ℝ), Real.exp (-t) * P.realizedHeatPointKernelTime x y t := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        exact Eventually.of_forall (fun t => by dsimp only; ring)
      rw [he, P.pointKernelLaplaceOne_eq, P.pointLocalTimeDiscountedPotential_symmetric y x 1]

theorem GraphShiftedContactOperatorProblem.borelDiscountedFuture_mean_resolventOne
    (P : GraphShiftedContactOperatorProblem V E) (hκ : ∀ v, P.strength v = 0)
    (x : GraphRealization P.geometry) (f : GraphRealization P.geometry → ℝ)
    (hf : Measurable f) {C : ℝ} (hC : ∀ z, ‖f z‖ ≤ C) :
    (∫ p, P.borelDiscountedFuture f 1 0 p ∂P.continuousPathLaw hκ x) = P.borelResolventOne f x :=
  (P.borelDiscountedFuture_mean_zero hκ x f hf hC (α := 1) (by norm_num)).trans
    (P.borelTransitionLaplace_one_eq x f hf hC)

end TimeTraps.Analysis
