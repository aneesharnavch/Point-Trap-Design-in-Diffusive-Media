module

public import TimeTraps.Analysis.StieltjesExponential
public import TimeTraps.Probability.StieltjesChainRule

@[expose] public section

/-! Continuous-weight Stieltjes substitution. The actual finite sums
are compared using a compact C1 Taylor error and the total increment of
the monotone integrator. In particular d(1-exp(-K)) has the same
continuous-weight integrals as exp(-K) dK on every finite positive horizon. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

theorem stieltjes_weighted_chainRule_error_tendsto (K J : StieltjesFunction ℝ)
    (hK : Continuous K) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hJ : ∀ r, J r = F (K r)) (g : ℝ≥0 → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    Tendsto (fun n => dyadicStieltjesSum J g T n -
      dyadicStieltjesSum K (fun t => g t * deriv F (K t.val)) T n) atTop (𝓝 0) := by
  let f : ℝ≥0 → ℝ := fun t => K t.val
  have hf : Continuous f := hK.comp continuous_subtype_val
  have hm : Monotone f := fun _ _ h => K.mono h
  let V : ℝ := K T.val - K 0
  have hV : 0 ≤ V := sub_nonneg.mpr (K.mono T.coe_nonneg)
  obtain ⟨R, hR⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hg.continuousOn : ContinuousOn g (Icc 0 T))
  let C : ℝ := max R 0 + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hb (n : ℕ) (i : Fin (2 ^ n + 1)) : |g (brownianDyadicGrid T n i)| ≤ C :=
    (hR _ (brownianDyadicGrid_mem_Icc T n i)).trans (by dsimp [C]; linarith [le_max_left R 0])
  have hrange (n : ℕ) (i : Fin (2 ^ n + 1)) :
      f (brownianDyadicGrid T n i) ∈ Icc (K 0) (K T.val) := by
    have hi := brownianDyadicGrid_mem_Icc T n i
    exact ⟨hm hi.1, hm hi.2⟩
  have hinc (n : ℕ) (i : Fin (2 ^ n)) :
      f (brownianDyadicGrid T n i.castSucc) ≤ f (brownianDyadicGrid T n i.succ) :=
    hm (brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i))
  have he (n : ℕ) : dyadicStieltjesSum J g T n -
      dyadicStieltjesSum K (fun t => g t * deriv F (K t.val)) T n =
      ∑ i : Fin (2 ^ n), (F (f (brownianDyadicGrid T n i.succ)) -
        F (f (brownianDyadicGrid T n i.castSucc)) -
        deriv F (f (brownianDyadicGrid T n i.castSucc)) *
          (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc))) *
          g (brownianDyadicGrid T n i.castSucc) := by
    unfold dyadicStieltjesSum
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [hJ, hJ]
    dsimp only [f]
    ring
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let η : ℝ := ε / (C * (V + 1))
  have hη : 0 < η := div_pos hε (mul_pos hC (by linarith))
  obtain ⟨δ, hδ, hc⟩ := stieltjesChainRule_remainder_compact hF (K 0) (K T.val) hη
  filter_upwards [dyadicPath_increments_eventually_small f T hf.continuousOn hδ] with n hn
  rw [Real.dist_eq, sub_zero, he]
  calc
    _ ≤ ∑ i : Fin (2 ^ n), |(F (f (brownianDyadicGrid T n i.succ)) -
        F (f (brownianDyadicGrid T n i.castSucc)) -
        deriv F (f (brownianDyadicGrid T n i.castSucc)) *
          (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc))) *
          g (brownianDyadicGrid T n i.castSucc)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin (2 ^ n), η *
        (f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc)) * C := by
      apply Finset.sum_le_sum
      intro i _
      have hs : f (brownianDyadicGrid T n i.succ) - f (brownianDyadicGrid T n i.castSucc) < δ := by
        simpa only [abs_of_nonneg (sub_nonneg.mpr (hinc n i))] using hn i
      rw [abs_mul]
      exact mul_le_mul (hc _ (hrange n i.castSucc) _ (hrange n i.succ) (hinc n i) hs)
        (hb n i.castSucc) (abs_nonneg _) (mul_nonneg hη.le (sub_nonneg.mpr (hinc n i)))
    _ = η * V * C := by
      rw [← Finset.sum_mul, ← Finset.mul_sum]
      have ht := finite_sum_increments
        (fun i : Fin (2 ^ n + 1) => f (brownianDyadicGrid T n i))
      have ht' : (∑ i : Fin (2 ^ n), (f (brownianDyadicGrid T n i.succ) -
          f (brownianDyadicGrid T n i.castSucc))) = V := by
        calc
          _ = f T - f 0 := by
            simpa only [brownianDyadicGrid_last, brownianDyadicGrid_zero] using ht
          _ = V := rfl
      exact congrArg (fun z : ℝ => η * z * C) ht'
    _ < ε := by
      have heq : η * (C * (V + 1)) = ε :=
        div_mul_cancel₀ ε (mul_ne_zero hC.ne' (by linarith))
      have hp : 0 < η * C := mul_pos hη hC
      nlinarith

theorem stieltjes_weighted_chainRule (K J : StieltjesFunction ℝ)
    (hK : Continuous K) {F : ℝ → ℝ} (hF : ContDiff ℝ 1 F)
    (hJ : ∀ r, J r = F (K r)) (g : ℝ≥0 → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal ∂J.measure) =
      ∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal * deriv F (K r) ∂K.measure := by
  have hd : Continuous (fun t : ℝ≥0 => g t * deriv F (K t.val)) :=
    hg.mul ((stieltjesChainRule_derivative_continuous hF).comp (hK.comp continuous_subtype_val))
  have hl := (dyadicStieltjesSum_tendsto J g hg T).sub (dyadicStieltjesSum_tendsto K _ hd T)
  have he := sub_eq_zero.mp (tendsto_nhds_unique hl
    (stieltjes_weighted_chainRule_error_tendsto K J hK hF hJ g hg T))
  calc
    _ = ∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal * deriv F (K r.toNNReal.val) ∂K.measure := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [Real.toNNReal_of_nonneg hr.1.le]
      rfl

theorem stieltjesExponential_weighted_integrable (K : StieltjesFunction ℝ)
    (hK : Continuous K) (g : ℝ≥0 → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    IntegrableOn (fun r => g r.toNNReal) (Ioc (0 : ℝ) T.val)
      (stieltjesExponential K hK).measure ∧
    IntegrableOn (fun r => g r.toNNReal * Real.exp (-K r)) (Ioc (0 : ℝ) T.val) K.measure :=
  ⟨(hg.comp continuous_real_toNNReal).integrableOn_Ioc,
    ((hg.comp continuous_real_toNNReal).mul (Real.continuous_exp.comp hK.neg)).integrableOn_Ioc⟩

theorem stieltjesExponential_weighted_integral (K : StieltjesFunction ℝ)
    (hK : Continuous K) (g : ℝ≥0 → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal ∂(stieltjesExponential K hK).measure) =
      ∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal * Real.exp (-K r) ∂K.measure := by
  have hF : ContDiff ℝ 1 (fun x : ℝ => 1 - Real.exp (-x)) := by fun_prop
  have hd : deriv (fun x : ℝ => 1 - Real.exp (-x)) = fun x => Real.exp (-x) := by
    funext x
    calc
      _ = 0 - Real.exp (-x) * (-1) :=
        ((hasDerivAt_const x 1).sub ((hasDerivAt_id x).neg.exp)).deriv
      _ = Real.exp (-x) := by ring
  have he := stieltjes_weighted_chainRule K (stieltjesExponential K hK) hK hF
    (stieltjesExponential_apply K hK) g hg T
  simpa only [hd] using he

theorem stieltjesExponential_integral (K : StieltjesFunction ℝ)
    (hK : Continuous K) (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, g r ∂(stieltjesExponential K hK).measure) =
      ∫ r in Ioc (0 : ℝ) T.val, g r * Real.exp (-K r) ∂K.measure := by
  have he := stieltjesExponential_weighted_integral K hK (fun t => g t.val)
    (hg.comp continuous_subtype_val) T
  have hg' (r : ℝ) (hr : r ∈ Ioc (0 : ℝ) T.val) : g r.toNNReal.val = g r := by
    rw [Real.toNNReal_of_nonneg hr.1.le]
    rfl
  calc
    _ = ∫ r in Ioc (0 : ℝ) T.val, g r.toNNReal.val ∂(stieltjesExponential K hK).measure := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact (hg' r hr).symm
    _ = _ := he
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      rw [hg' r hr]

end TimeTraps.Probability
