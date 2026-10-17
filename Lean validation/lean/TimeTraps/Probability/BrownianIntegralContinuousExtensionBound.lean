module

public import TimeTraps.Probability.BrownianIntegralCompactMaximal

@[expose] public section

/-! The compact maximal estimate depends only on the fixed-time
martingale evaluations of a continuous-path L² variable. This form also
applies to finite linear combinations of elementary path variables. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

abbrev BrownianCompactPathL2 (T : ℝ≥0) :=
  Lp C(BrownianCompactTime T, ℝ) 2 brownianDyadicMeasure

def brownianCompactEvaluation (T : ℝ≥0) (t : BrownianCompactTime T) :
    BrownianCompactPathL2 T →L[ℝ] Lp ℝ 2 brownianDyadicMeasure :=
  (ContinuousMap.evalCLM ℝ t).compLpL 2 brownianDyadicMeasure

theorem brownianCompactEvaluation_coe (T : ℝ≥0) (t : BrownianCompactTime T)
    (F : BrownianCompactPathL2 T) :
    brownianCompactEvaluation T t F =ᵐ[brownianDyadicMeasure] (fun ω => F ω t) :=
  (ContinuousMap.evalCLM ℝ t : C(BrownianCompactTime T, ℝ) →L[ℝ] ℝ).coeFn_compLpL F

def brownianCompactMaxApprox {T : ℝ≥0} (F : BrownianCompactPathL2 T)
    (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  finiteRunningMax (fun k => ‖F ω (denseSeq (BrownianCompactTime T) k)‖) n

theorem brownianCompactMaxApprox_memLp {T : ℝ≥0} (F : BrownianCompactPathL2 T) (n : ℕ) :
    MemLp (brownianCompactMaxApprox F n) 2 brownianDyadicMeasure := by
  apply finiteRunningMax_memLp
  intro k
  exact ((ContinuousMap.evalCLM ℝ (denseSeq (BrownianCompactTime T) k) :
    C(BrownianCompactTime T, ℝ) →L[ℝ] ℝ).comp_memLp F).norm

theorem brownianCompactMaxApprox_secondMoment_le {T : ℝ≥0}
    (F : BrownianCompactPathL2 T) (f : BrownianIntegrand)
    (hF : ∀ t : BrownianCompactTime T, (fun ω => F ω t) =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralProcess f t.val) (n : ℕ) :
    (∫ ω, brownianCompactMaxApprox F n ω ^ 2 ∂brownianDyadicMeasure) ≤
      4 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
        brownianDyadicMeasure T f‖ ^ 2 := by
  classical
  let τ : ℕ → ℝ≥0 := fun k => (denseSeq (BrownianCompactTime T) k).val
  let s := (Finset.range (n + 1)).image τ
  have hs : s.Nonempty := ⟨τ 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
  have hT : ∀ t ∈ s, t ≤ T := by
    intro t ht
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    exact (denseSeq (BrownianCompactTime T) k).property.2
  let g := brownianIntegralFiniteMax brownianDyadicPath_isPreBrownianReal f s hs
  have hg2 : MemLp g 2 brownianDyadicMeasure :=
    brownianIntegralFiniteMax_memLp brownianDyadicPath_isPreBrownianReal f s hs
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
  have hsq : (fun ω => brownianCompactMaxApprox F n ω ^ 2) ≤ᵐ[brownianDyadicMeasure]
      (fun ω => g ω ^ 2) := by
    filter_upwards [hle] with ω hω
    have hn : 0 ≤ brownianCompactMaxApprox F n ω :=
      finiteRunningMax_nonneg (fun k => ‖F ω (denseSeq (BrownianCompactTime T) k)‖) (norm_nonneg _) n
    exact (sq_le_sq₀ hn (hn.trans hω)).mpr hω
  exact (integral_mono_ae (brownianCompactMaxApprox_memLp F n).integrable_sq
    hg2.integrable_sq hsq).trans
      (brownianIntegralFiniteMax_le_norm brownianDyadicPath_isPreBrownianReal f s hs T hT)

theorem brownianCompactPathL2_norm_sq (T : ℝ≥0) (F : BrownianCompactPathL2 T) :
    ‖F‖ ^ 2 = ∫ ω, ‖F ω‖ ^ 2 ∂brownianDyadicMeasure := by
  have he : ‖(Lp.memLp F).norm.toLp (fun ω => ‖F ω‖)‖ = ‖F‖ := by
    rw [Lp.norm_toLp, Lp.norm_def, eLpNorm_norm]
  rw [← he, TimeTraps.Analysis.memLp_norm_toLp_sq]

theorem brownianCompactPathL2_norm_le {T : ℝ≥0}
    (F : BrownianCompactPathL2 T) (f : BrownianIntegrand)
    (hF : ∀ t : BrownianCompactTime T, (fun ω => F ω t) =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralProcess f t.val) :
    ‖F‖ ≤ 2 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure T f‖ := by
  have hb : ∀ n, (∫ ω, brownianCompactMaxApprox F n ω ^ 2 ∂brownianDyadicMeasure) ≤
      (2 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
        brownianDyadicMeasure T f‖) ^ 2 := by
    intro n
    convert brownianCompactMaxApprox_secondMoment_le F f hF n using 1
    ring
  have hlim : ∀ᵐ ω ∂brownianDyadicMeasure,
      Tendsto (fun n => brownianCompactMaxApprox F n ω) atTop (𝓝 ‖F ω‖) :=
    Eventually.of_forall (fun ω => compactPath_runningMax_tendsto (F ω)
      (denseSeq (BrownianCompactTime T)) (denseRange_denseSeq (BrownianCompactTime T)))
  have h := compactMaximal_memLp_of_tendsto (by positivity)
    (brownianCompactMaxApprox_memLp F) (Lp.memLp F).norm.1 hlim hb
  apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
  rw [brownianCompactPathL2_norm_sq]
  exact h.2

end TimeTraps.Probability

end
