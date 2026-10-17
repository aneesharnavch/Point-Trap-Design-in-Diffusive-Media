module

public import TimeTraps.Analysis.StieltjesChainRuleRemainder
public import TimeTraps.Probability.DyadicStieltjesIntegral
public import TimeTraps.Probability.BrownianItoC2Remainder
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

@[expose] public section

/-! The continuous Stieltjes chain rule, proved by actual finite
telescoping and convergence of dyadic Stieltjes sums. The integrator
may be singular: only its continuity and monotonicity are used. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem stieltjes_chainRule_integrable (K : StieltjesFunction ℝ)
    (hK : Continuous K) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (T : ℝ≥0) :
    IntegrableOn (fun r => deriv F (K r)) (Ioc (0 : ℝ) T.val) K.measure :=
  ((stieltjesChainRule_derivative_continuous hF).comp hK).integrableOn_Ioc

theorem stieltjes_chainRule_sums_tendsto (K : StieltjesFunction ℝ)
    (hK : Continuous K) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (T : ℝ≥0) :
    Tendsto (dyadicStieltjesSum K (fun t => deriv F (K t.val)) T) atTop
      (𝓝 (F (K T.val) - F (K 0))) := by
  let f : ℝ≥0 → ℝ := fun t => K t.val
  have hf : Continuous f := hK.comp continuous_subtype_val
  have hm : Monotone f := fun _ _ h => K.mono h
  let V : ℝ := K T.val - K 0
  have hV : 0 ≤ V := sub_nonneg.mpr (K.mono T.coe_nonneg)
  have hrange (n : ℕ) (i : Fin (2 ^ n + 1)) :
      f (brownianDyadicGrid T n i) ∈ Icc (K 0) (K T.val) := by
    have hi := brownianDyadicGrid_mem_Icc T n i
    exact ⟨hm hi.1, hm hi.2⟩
  have hinc (n : ℕ) (i : Fin (2 ^ n)) :
      f (brownianDyadicGrid T n i.castSucc) ≤ f (brownianDyadicGrid T n i.succ) :=
    hm (brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i))
  have htel (n : ℕ) :
      (∑ i : Fin (2 ^ n), (F (f (brownianDyadicGrid T n i.succ)) -
        F (f (brownianDyadicGrid T n i.castSucc)))) = F (K T.val) - F (K 0) := by
    have he := finite_sum_increments
      (fun i : Fin (2 ^ n + 1) => F (f (brownianDyadicGrid T n i)))
    calc
      _ = F (f T) - F (f 0) := by
        simpa only [brownianDyadicGrid_last, brownianDyadicGrid_zero] using he
      _ = _ := rfl
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (V + 1)
  have hη : 0 < η := div_pos hε (by linarith)
  obtain ⟨δ, hδ, hc⟩ := stieltjesChainRule_remainder_compact hF (K 0) (K T.val) hη
  filter_upwards [dyadicPath_increments_eventually_small f T hf.continuousOn hδ] with n hn
  have he : dyadicStieltjesSum K (fun t => deriv F (K t.val)) T n -
      (F (K T.val) - F (K 0)) =
      ∑ i : Fin (2 ^ n), ((f (brownianDyadicGrid T n i.succ) -
        f (brownianDyadicGrid T n i.castSucc)) * deriv F (f (brownianDyadicGrid T n i.castSucc)) -
        (F (f (brownianDyadicGrid T n i.succ)) - F (f (brownianDyadicGrid T n i.castSucc)))) := by
    rw [Finset.sum_sub_distrib, htel]
    rfl
  rw [Real.dist_eq, he]
  calc
    _ ≤ ∑ i : Fin (2 ^ n), |(f (brownianDyadicGrid T n i.succ) -
        f (brownianDyadicGrid T n i.castSucc)) * deriv F (f (brownianDyadicGrid T n i.castSucc)) -
        (F (f (brownianDyadicGrid T n i.succ)) - F (f (brownianDyadicGrid T n i.castSucc)))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (2 ^ n), η * (f (brownianDyadicGrid T n i.succ) -
        f (brownianDyadicGrid T n i.castSucc)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_sub_comm, mul_comm]
      apply hc _ (hrange n i.castSucc) _ (hrange n i.succ) (hinc n i)
      simpa only [abs_of_nonneg (sub_nonneg.mpr (hinc n i))] using hn i
    _ = η * V := by
      rw [← Finset.mul_sum]
      have he := finite_sum_increments
        (fun i : Fin (2 ^ n + 1) => f (brownianDyadicGrid T n i))
      have he' : (∑ i : Fin (2 ^ n), (f (brownianDyadicGrid T n i.succ) -
          f (brownianDyadicGrid T n i.castSucc))) = V := by
        calc
          _ = f T - f 0 := by
            simpa only [brownianDyadicGrid_last, brownianDyadicGrid_zero] using he
          _ = V := rfl
      exact congrArg (fun z : ℝ => η * z) he'
    _ < ε := by
      have he : η * (V + 1) = ε := div_mul_cancel₀ ε (by linarith : V + 1 ≠ 0)
      nlinarith

theorem stieltjes_chainRule (K : StieltjesFunction ℝ)
    (hK : Continuous K) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, deriv F (K r) ∂K.measure) =
      F (K T.val) - F (K 0) := by
  have hg : Continuous (fun t : ℝ≥0 => deriv F (K t.val)) :=
    (stieltjesChainRule_derivative_continuous hF).comp (hK.comp continuous_subtype_val)
  have he := tendsto_nhds_unique (dyadicStieltjesSum_tendsto K _ hg T)
    (stieltjes_chainRule_sums_tendsto K hK hF T)
  calc
    _ = ∫ r in Ioc (0 : ℝ) T.val, deriv F (K r.toNNReal.val) ∂K.measure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.toNNReal_of_nonneg hr.1.le]
      rfl
    _ = _ := he

theorem stieltjes_exp_neg_integrable (K : StieltjesFunction ℝ)
    (hK : Continuous K) (T : ℝ≥0) :
    IntegrableOn (fun r => Real.exp (-K r)) (Ioc (0 : ℝ) T.val) K.measure :=
  (Real.continuous_exp.comp hK.neg).integrableOn_Ioc

theorem stieltjes_exp_neg_integral (K : StieltjesFunction ℝ)
    (hK : Continuous K) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, Real.exp (-K r) ∂K.measure) =
      Real.exp (-K 0) - Real.exp (-K T.val) := by
  have hF : ContDiff ℝ 1 (fun x : ℝ => -Real.exp (-x)) := by fun_prop
  have hd : deriv (fun x : ℝ => -Real.exp (-x)) = fun x => Real.exp (-x) := by
    funext x
    simpa using (((hasDerivAt_id x).neg.exp).neg).deriv
  have he := stieltjes_chainRule K hK hF T
  rw [hd] at he
  simpa only [neg_sub_neg] using he

end TimeTraps.Probability
