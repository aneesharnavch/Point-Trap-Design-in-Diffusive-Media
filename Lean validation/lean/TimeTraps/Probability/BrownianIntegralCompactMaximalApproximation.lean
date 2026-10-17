module

public import TimeTraps.Probability.BrownianIntegralCompactMaximalPath
public import TimeTraps.Probability.BrownianIntegralCompactMaximalTopology
public import TimeTraps.Probability.BrownianIntegralCompactMaximalFinite

@[expose] public section

/-! Finite dense-time maxima converge to the actual compact supremum.
Every finite approximation obeys the same constant-four second-moment
bound, by the checked finite-set maximal inequality. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

variable {I : Type*} [Fintype I]

theorem brownianElementaryCompactPath_stronglyMeasurable (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) : StronglyMeasurable (brownianElementaryCompactPath a T) :=
  compactPath_stronglyMeasurable _ (fun t => brownianElementaryRegularPath_measurable a t.val)

theorem brownianElementaryCompactMax_measurable (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) : Measurable (brownianElementaryCompactMax a T) :=
  compactPath_norm_measurable _ (fun t => brownianElementaryRegularPath_measurable a t.val)

theorem brownianElementaryCompactPath_eval_memLp (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) (t : BrownianCompactTime T) :
    MemLp (fun ω => brownianElementaryCompactPath a T ω t) 2 brownianDyadicMeasure :=
  (brownianIntegralProcess_memLp brownianDyadicPath_isPreBrownianReal
    (brownianElementarySumIntegrand a) t.val).ae_eq (brownianElementaryRegularPath_martingale_ae a t.val).symm

def brownianElementaryCompactMaxApprox (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) (n : ℕ) (ω : ℕ → ℝ) : ℝ :=
  finiteRunningMax (fun k => ‖brownianElementaryCompactPath a T ω (denseSeq (BrownianCompactTime T) k)‖) n

theorem brownianElementaryCompactMaxApprox_memLp (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) (n : ℕ) :
    MemLp (brownianElementaryCompactMaxApprox a T n) 2 brownianDyadicMeasure :=
  finiteRunningMax_memLp (fun k => (brownianElementaryCompactPath_eval_memLp a T
    (denseSeq (BrownianCompactTime T) k)).norm) n

theorem brownianElementaryCompactMaxApprox_tendsto (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) (ω : ℕ → ℝ) :
    Tendsto (fun n => brownianElementaryCompactMaxApprox a T n ω) atTop
      (𝓝 (brownianElementaryCompactMax a T ω)) :=
  compactPath_runningMax_tendsto (brownianElementaryCompactPath a T ω)
    (denseSeq (BrownianCompactTime T)) (denseRange_denseSeq (BrownianCompactTime T))

theorem brownianElementaryCompactMaxApprox_secondMoment_le (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) (n : ℕ) :
    (∫ ω, brownianElementaryCompactMaxApprox a T n ω ^ 2 ∂brownianDyadicMeasure) ≤
      4 * ‖brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable
        brownianDyadicMeasure T (brownianElementarySumIntegrand a)‖ ^ 2 := by
  classical
  let τ : ℕ → ℝ≥0 := fun k => (denseSeq (BrownianCompactTime T) k).val
  let s := (Finset.range (n + 1)).image τ
  have hs : s.Nonempty := ⟨τ 0, Finset.mem_image.mpr ⟨0, by simp, rfl⟩⟩
  have hT : ∀ t ∈ s, t ≤ T := by
    intro t ht
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp ht
    exact (denseSeq (BrownianCompactTime T) k).property.2
  let g := brownianIntegralFiniteMax brownianDyadicPath_isPreBrownianReal
    (brownianElementarySumIntegrand a) s hs
  have hg2 : MemLp g 2 brownianDyadicMeasure :=
    brownianIntegralFiniteMax_memLp brownianDyadicPath_isPreBrownianReal _ s hs
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ k : ℕ,
      brownianElementaryRegularPath a (τ k) ω =
        brownianStochasticIntegralProcess (brownianElementarySumIntegrand a) (τ k) ω :=
    ae_all_iff.mpr (fun k => brownianElementaryRegularPath_martingale_ae a (τ k))
  have hle : brownianElementaryCompactMaxApprox a T n ≤ᵐ[brownianDyadicMeasure] g := by
    filter_upwards [hall] with ω hω
    apply (finiteRunningMax_le_iff _ n _).mpr
    intro k hk
    have he : ‖brownianElementaryCompactPath a T ω (denseSeq (BrownianCompactTime T) k)‖ =
        |brownianStochasticIntegralProcess (brownianElementarySumIntegrand a) (τ k) ω| := by
      change |brownianElementaryRegularPath a (τ k) ω| = _
      rw [hω k]
    rw [he]
    exact Finset.le_sup' (fun t => |brownianIntegralProcess brownianDyadicPath_isPreBrownianReal
      (brownianElementarySumIntegrand a) t ω|)
      (Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (Nat.lt_succ_of_le hk), rfl⟩)
  have hsq : (fun ω => brownianElementaryCompactMaxApprox a T n ω ^ 2) ≤ᵐ[brownianDyadicMeasure]
      (fun ω => g ω ^ 2) := by
    filter_upwards [hle] with ω hω
    have hn : 0 ≤ brownianElementaryCompactMaxApprox a T n ω :=
      finiteRunningMax_nonneg
        (fun k => ‖brownianElementaryCompactPath a T ω (denseSeq (BrownianCompactTime T) k)‖)
        (norm_nonneg _) n
    exact (sq_le_sq₀ hn (hn.trans hω)).mpr hω
  exact (integral_mono_ae (brownianElementaryCompactMaxApprox_memLp a T n).integrable_sq
    hg2.integrable_sq hsq).trans
      (brownianIntegralFiniteMax_le_norm brownianDyadicPath_isPreBrownianReal _ s hs T hT)

end TimeTraps.Probability

end
