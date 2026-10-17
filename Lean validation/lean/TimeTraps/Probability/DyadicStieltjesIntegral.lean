module

public import TimeTraps.Probability.DyadicStieltjesSum
public import TimeTraps.Probability.ContinuousMonotoneQuadraticVariation
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

@[expose] public section

/-! Continuous weights have convergent actual left dyadic Stieltjes
sums. The proof is dominated convergence under the finite restricted
Stieltjes measure. A compact-time truncation removes any global bound
on the weight. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem dyadicStieltjesSum_tendsto_bounded (K : StieltjesFunction ℝ) (g : ℝ≥0 → ℝ)
    (hg : Continuous g) {M : ℝ≥0} (hb : ∀ t, |g t| ≤ M.val) (T : ℝ≥0) :
    Tendsto (dyadicStieltjesSum K g T) atTop
      (𝓝 (∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal ∂K.measure)) := by
  have : IsFiniteMeasure (K.measure.restrict (Ioc (0 : ℝ) T.val)) :=
    ⟨by rw [Measure.restrict_apply_univ, K.measure_Ioc]; exact ENNReal.ofReal_lt_top⟩
  have hm (n : ℕ) : Measurable (fun r =>
      brownianSquareStepProcess (fun t (_ : Unit) => g t) T n (r, ())) := by
    change Measurable (fun r => ∑ i : Fin (2 ^ n),
      brownianIntervalIndicator (brownianDyadicGrid T n i.castSucc)
        (brownianDyadicGrid T n i.succ) r * g (brownianDyadicGrid T n i.castSucc))
    exact Finset.measurable_sum _ (fun (i : Fin (2 ^ n)) _ =>
      (brownianIntervalIndicator_measurable _ _).mul_const _)
  have hd := tendsto_integral_of_dominated_convergence (fun _ : ℝ => M.val)
    (fun n => (hm n).aestronglyMeasurable)
    (integrable_const M.val : Integrable (fun _ : ℝ => M.val)
      (K.measure.restrict (Ioc (0 : ℝ) T.val)))
    (fun n => by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      have h := brownianAdaptedContinuous_step_bound (fun t (_ : Unit) => hb t) T n (r, ())
      change |brownianSquareStepProcess (fun t (_ : Unit) => g t) T n (r, ())| ≤
        M.val * (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) r at h
      rw [Set.indicator_of_mem hr, mul_one] at h
      exact h)
    (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      simpa only [brownianSquareProcess, Set.indicator_of_mem hr, one_mul] using
        brownianSquareStepProcess_tendsto_at (fun t (_ : Unit) => g t) T (r, ())
          (fun _ => hg.continuousAt))
  simpa only [dyadicStieltjesStep_integral] using hd

theorem dyadicStieltjesSum_tendsto (K : StieltjesFunction ℝ) (g : ℝ≥0 → ℝ)
    (hg : Continuous g) (T : ℝ≥0) :
    Tendsto (dyadicStieltjesSum K g T) atTop
      (𝓝 (∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal ∂K.measure)) := by
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.continuousOn : ContinuousOn g (Icc 0 T))
  let C : ℝ≥0 → ℝ := fun t => g (min t T)
  have hC : Continuous C := hg.comp (continuous_id.min continuous_const)
  have hb (t : ℝ≥0) : |C t| ≤ (⟨max R 0, le_max_right R 0⟩ : ℝ≥0).val :=
    (hR (min t T) ⟨by positivity, min_le_right _ _⟩).trans (le_max_left _ _)
  have hs (n : ℕ) : dyadicStieltjesSum K C T n = dyadicStieltjesSum K g T n := by
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [C]
    rw [min_eq_left (brownianDyadicGrid_mem_Icc T n i.castSucc).2]
  have hi : (∫ r in Ioc (0 : ℝ) T.val, C r.toNNReal ∂K.measure) =
      ∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal ∂K.measure := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have ht : r.toNNReal ≤ T := by
      exact Real.toNNReal_le_iff_le_coe.mpr hr.2
    exact congrArg g (min_eq_left ht)
  have hf : dyadicStieltjesSum K C T = dyadicStieltjesSum K g T := funext hs
  simpa only [hf, hi] using dyadicStieltjesSum_tendsto_bounded K C hC hb T

end TimeTraps.Probability
