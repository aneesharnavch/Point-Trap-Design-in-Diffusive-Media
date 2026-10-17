module

public import TimeTraps.Probability.BrownianIntegralFourthCompactData
public import TimeTraps.Probability.BrownianIntegralFourthLimit
public import TimeTraps.Probability.BrownianIntegralContinuousExtensionPath

@[expose] public section

/-! Fourth-moment Doob bound on the actual continuous compact-time
integral. A countable dense sequence, followed by Fatou, controls the
whole interval and derives fourth integrability of its supremum. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TopologicalSpace
open scoped NNReal ENNReal Topology

theorem brownianCompactMaxApprox_fourth {T : ℝ≥0}
    (F : BrownianCompactPathL2 T) (f : BrownianIntegrand)
    (hF : ∀ t : BrownianCompactTime T, (fun ω => F ω t) =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralProcess f t.val)
    (h4 : ∀ t ≤ T, MemLp (brownianStochasticIntegralProcess f t) 4 brownianDyadicMeasure)
    (n : ℕ) : MemLp (brownianCompactMaxApprox F n) 4 brownianDyadicMeasure ∧
    (∫ ω, brownianCompactMaxApprox F n ω ^ 4 ∂brownianDyadicMeasure) ≤
      4 * ∫ ω, brownianStochasticIntegralProcess f T ω ^ 4 ∂brownianDyadicMeasure := by
  classical
  let τ : ℕ → ℝ≥0 := fun k => (denseSeq (BrownianCompactTime T) k).val
  let s := (Finset.range (n + 1)).image τ
  have hs : s.Nonempty := ⟨τ 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
  have hT : ∀ t ∈ s, t ≤ T := by
    intro t ht
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    exact (denseSeq (BrownianCompactTime T) k).property.2
  let g := brownianIntegralFiniteMax brownianDyadicPath_isPreBrownianReal f s hs
  have hg := brownianIntegralFiniteMax_fourth brownianDyadicPath_isPreBrownianReal f s hs T hT h4
  have hmem : MemLp (brownianCompactMaxApprox F n) 4 brownianDyadicMeasure := by
    apply finiteRunningMax_memLp_four
    intro k
    exact ((h4 _ (denseSeq (BrownianCompactTime T) k).property.2).ae_eq
      (hF (denseSeq (BrownianCompactTime T) k)).symm).norm
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ k : ℕ,
      F ω (denseSeq (BrownianCompactTime T) k) = brownianStochasticIntegralProcess f (τ k) ω :=
    ae_all_iff.mpr (fun k => hF (denseSeq (BrownianCompactTime T) k))
  have hle : brownianCompactMaxApprox F n ≤ᵐ[brownianDyadicMeasure] g := by
    filter_upwards [hall] with ω hω
    apply (finiteRunningMax_le_iff _ n _).mpr
    intro k hk
    rw [hω k, Real.norm_eq_abs]
    exact Finset.le_sup' (fun t => |brownianIntegralProcess brownianDyadicPath_isPreBrownianReal f t ω|)
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)
  refine ⟨hmem, (integral_mono_ae (brownian_memLp_four_integrable_fourth hmem)
    (brownian_memLp_four_integrable_fourth hg.1) ?_).trans hg.2⟩
  filter_upwards [hle] with ω hω
  have hn : 0 ≤ brownianCompactMaxApprox F n ω :=
    finiteRunningMax_nonneg (fun k => ‖F ω (denseSeq (BrownianCompactTime T) k)‖) (norm_nonneg _) n
  exact pow_le_pow_left₀ hn hω 4

theorem brownianCompactPathL2_fourth {T : ℝ≥0}
    (F : BrownianCompactPathL2 T) (f : BrownianIntegrand)
    (hF : ∀ t : BrownianCompactTime T, (fun ω => F ω t) =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralProcess f t.val)
    (h4 : ∀ t ≤ T, MemLp (brownianStochasticIntegralProcess f t) 4 brownianDyadicMeasure) :
    MemLp (fun ω => ‖F ω‖) 4 brownianDyadicMeasure ∧
    (∫ ω, ‖F ω‖ ^ 4 ∂brownianDyadicMeasure) ≤
      4 * ∫ ω, brownianStochasticIntegralProcess f T ω ^ 4 ∂brownianDyadicMeasure := by
  have hlim : ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun n => brownianCompactMaxApprox F n ω) atTop (𝓝 ‖F ω‖) :=
    Eventually.of_forall (fun ω => compactPath_runningMax_tendsto (F ω)
      (denseSeq (BrownianCompactTime T)) (denseRange_denseSeq (BrownianCompactTime T)))
  exact brownian_fourth_bound_of_ae_tendsto_varying
    (mul_nonneg (by norm_num) (integral_nonneg (fun ω => by positivity)))
    (fun n => (brownianCompactMaxApprox_fourth F f hF h4 n).1) (Lp.memLp F).norm.1 hlim
    (fun n => (brownianCompactMaxApprox_fourth F f hF h4 n).2) tendsto_const_nhds

theorem brownianIntegralCompactNorm_fourth (T : ℝ≥0) (f : BrownianIntegrand)
    (h4 : ∀ t ≤ T, MemLp (brownianStochasticIntegralProcess f t) 4 brownianDyadicMeasure) :
    MemLp (fun ω => ‖brownianIntegralContinuousL2 T f ω‖) 4 brownianDyadicMeasure ∧
    (∫ ω, ‖brownianIntegralContinuousL2 T f ω‖ ^ 4 ∂brownianDyadicMeasure) ≤
      4 * ∫ ω, brownianStochasticIntegralProcess f T ω ^ 4 ∂brownianDyadicMeasure :=
  brownianCompactPathL2_fourth _ f (brownianIntegralContinuousPath_martingale_ae T f) h4

end TimeTraps.Probability
