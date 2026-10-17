module

public import TimeTraps.Probability.DyadicWeightedIncrement
public import TimeTraps.Probability.BrownianAdaptedContinuousProcess
public import Mathlib.MeasureTheory.Integral.DominatedConvergence
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! Weighted dyadic increments of an actual time primitive converge to
the ordinary weighted time integral. Both paths may be signed. The proof
uses exact interval increments, finite step integration and dominated
convergence on a compact time interval; no stochastic assumption is used. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal Topology

noncomputable def nnrealTimePrimitive (v : ℝ≥0 → ℝ) (t : ℝ≥0) : ℝ :=
  ∫ r in (0 : ℝ)..t.val, v r.toNNReal

theorem nnrealTimePrimitive_increment (v : ℝ≥0 → ℝ) (hv : Continuous v) (s t : ℝ≥0) :
    nnrealTimePrimitive v t - nnrealTimePrimitive v s =
      ∫ r in s.val..t.val, v r.toNNReal := by
  have hc := hv.comp continuous_real_toNNReal
  exact intervalIntegral.integral_interval_sub_left
    (hc.intervalIntegrable 0 t.val) (hc.intervalIntegrable 0 s.val)

theorem dyadicTimePrimitiveStep_integral (H v : ℝ≥0 → ℝ) (hv : Continuous v)
    (T : ℝ≥0) (n : ℕ) :
    (∫ r in Ioc (0 : ℝ) T.val,
      brownianSquareStepProcess (fun t (_ : Unit) => H t) T n (r, ()) * v r.toNNReal) =
      dyadicWeightedIncrement H (nnrealTimePrimitive v) T n := by
  have hc := hv.comp continuous_real_toNNReal
  have hind (s t : ℝ≥0) :
      (fun r => brownianIntervalIndicator s t r * v r.toNNReal) =
        (Ioc s.val t.val).indicator (fun r => v r.toNNReal) := by
    funext r
    by_cases hr : r ∈ Ioc s.val t.val
    · simp only [brownianIntervalIndicator, Set.indicator_of_mem hr, one_mul]
    · simp only [brownianIntervalIndicator, Set.indicator_of_notMem hr, zero_mul]
  have hi (s t : ℝ≥0) : Integrable (fun r => brownianIntervalIndicator s t r * v r.toNNReal) := by
    rw [hind]
    exact (integrable_indicator_iff measurableSet_Ioc).mpr (hc.intervalIntegrable s.val t.val).1
  have hval (s t : ℝ≥0) (hst : s ≤ t) :
      (∫ r, brownianIntervalIndicator s t r * v r.toNNReal) =
        nnrealTimePrimitive v t - nnrealTimePrimitive v s := by
    rw [hind, integral_indicator measurableSet_Ioc, nnrealTimePrimitive_increment v hv,
      intervalIntegral.integral_of_le (show s.val ≤ t.val from hst)]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero (fun r hr => by
    rw [brownianSquareStepProcess_outside (fun t (_ : Unit) => H t) T n () hr, zero_mul])]
  calc
    _ = ∫ r, ∑ i : Fin (2 ^ n), H (brownianDyadicGrid T n i.castSucc) *
        (brownianIntervalIndicator (brownianDyadicGrid T n i.castSucc)
          (brownianDyadicGrid T n i.succ) r * v r.toNNReal) := by
      apply integral_congr_ae
      filter_upwards [] with r
      change (∑ i : Fin (2 ^ n),
        brownianIntervalIndicator (brownianDyadicGrid T n i.castSucc)
          (brownianDyadicGrid T n i.succ) r * H (brownianDyadicGrid T n i.castSucc)) * _ = _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ i : Fin (2 ^ n), H (brownianDyadicGrid T n i.castSucc) *
        (nnrealTimePrimitive v (brownianDyadicGrid T n i.succ) -
          nnrealTimePrimitive v (brownianDyadicGrid T n i.castSucc)) := by
      rw [integral_finsetSum _ (fun (i : Fin (2 ^ n)) _ =>
        (hi (brownianDyadicGrid T n i.castSucc) (brownianDyadicGrid T n i.succ)).const_mul _)]
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_const_mul, hval _ _ (brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i))]
    _ = _ := rfl

theorem dyadicWeightedIncrement_timePrimitive_tendsto (H v : ℝ≥0 → ℝ)
    (hH : Continuous H) (hv : Continuous v) (T : ℝ≥0) :
    Tendsto (fun n => dyadicWeightedIncrement H (nnrealTimePrimitive v) T n) atTop
      (𝓝 (∫ r in (0 : ℝ)..T.val, H r.toNNReal * v r.toNNReal)) := by
  have hc := hv.comp continuous_real_toNNReal
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hH.continuousOn : ContinuousOn H (Icc 0 T))
  have hm (n : ℕ) : Measurable (fun r : ℝ =>
      brownianSquareStepProcess (fun t (_ : Unit) => H t) T n (r, ()) * v r.toNNReal) := by
    have hs : Measurable (fun r : ℝ =>
        brownianSquareStepProcess (fun t (_ : Unit) => H t) T n (r, ())) := by
      change Measurable (fun r => ∑ i : Fin (2 ^ n),
        brownianIntervalIndicator (brownianDyadicGrid T n i.castSucc)
          (brownianDyadicGrid T n i.succ) r * H (brownianDyadicGrid T n i.castSucc))
      exact Finset.measurable_sum _ (fun (i : Fin (2 ^ n)) _ =>
        (brownianIntervalIndicator_measurable _ _).mul_const _)
    exact hs.mul hc.measurable
  have hd := tendsto_integral_of_dominated_convergence
    (μ := (volume : Measure ℝ).restrict (Ioc (0 : ℝ) T.val))
    (fun r : ℝ => max R 0 * ‖v r.toNNReal‖)
    (fun n => (hm n).aestronglyMeasurable)
    ((hc.intervalIntegrable 0 T.val).1.norm.const_mul (max R 0))
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      obtain ⟨i, hi⟩ := brownianDyadicGrid_cell T n hr
      rw [norm_mul, brownianSquareStepProcess_cell (fun t (_ : Unit) => H t) T n () i hi]
      exact mul_le_mul_of_nonneg_right
        ((hR (brownianDyadicGrid T n i.castSucc) (brownianDyadicGrid_mem_Icc T n i.castSucc)).trans
          (le_max_left R 0)) (norm_nonneg _))
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have hl := (brownianSquareStepProcess_tendsto_at (fun t (_ : Unit) => H t) T (r, ())
        (fun _ => hH.continuousAt)).mul_const (v r.toNNReal)
      simpa only [brownianSquareProcess, Set.indicator_of_mem hr, one_mul] using hl)
  have hf : Tendsto (fun n => dyadicWeightedIncrement H (nnrealTimePrimitive v) T n) atTop
      (𝓝 (∫ r in Ioc (0 : ℝ) T.val, H r.toNNReal * v r.toNNReal)) := by
    simpa only [dyadicTimePrimitiveStep_integral H v hv T] using hd
  convert hf using 1
  exact congrArg (fun z : ℝ => 𝓝 z) (intervalIntegral.integral_of_le T.coe_nonneg)

end TimeTraps.Probability
