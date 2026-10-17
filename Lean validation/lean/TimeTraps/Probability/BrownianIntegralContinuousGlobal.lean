module

public import TimeTraps.Probability.BrownianIntegralContinuousGlobalCompatibility

@[expose] public section

/-! A single continuous stochastic integral process on all nonnegative
times. Integer-horizon paths are glued on their proved measurable
compatibility event, and the process is zero on its null complement. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

def brownianIntegralHorizonIndex (t : ℝ≥0) : ℕ := ⌈t.val⌉₊

theorem brownianIntegralHorizonIndex_bound (t : ℝ≥0) : t ≤ (brownianIntegralHorizonIndex t : ℝ≥0) := by
  exact_mod_cast Nat.le_ceil t.val

def brownianIntegralGlobalPath (f : BrownianIntegrand) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ := by
  classical
  exact if brownianIntegralGlobalCompatible f ω then
    brownianIntegralHorizonPath (brownianIntegralHorizonIndex t) f t ω else 0

theorem brownianIntegralGlobalPath_eq_horizon {f : BrownianIntegrand} {ω : ℕ → ℝ}
    (hω : brownianIntegralGlobalCompatible f ω) (n : ℕ) (t : ℝ≥0) (ht : t ≤ n) :
    brownianIntegralGlobalPath f t ω = brownianIntegralHorizonPath n f t ω := by
  simp only [brownianIntegralGlobalPath, if_pos hω]
  exact brownianIntegralGlobalCompatible_eq hω (brownianIntegralHorizonIndex t) n t
    (brownianIntegralHorizonIndex_bound t) ht

theorem brownianIntegralGlobalPath_continuous (f : BrownianIntegrand) (ω : ℕ → ℝ) :
    Continuous (fun t => brownianIntegralGlobalPath f t ω) := by
  by_cases hω : brownianIntegralGlobalCompatible f ω
  · apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt t.val
    have ht : t < (n : ℝ≥0) := by exact_mod_cast hn
    apply (brownianIntegralHorizonPath_continuous n f ω).continuousAt.congr_of_eventuallyEq
    filter_upwards [Iic_mem_nhds ht] with s hs
    exact brownianIntegralGlobalPath_eq_horizon hω n s hs
  · simp only [brownianIntegralGlobalPath, if_neg hω]
    exact continuous_const

theorem brownianIntegralGlobalPath_measurable (f : BrownianIntegrand) (t : ℝ≥0) :
    Measurable (brownianIntegralGlobalPath f t) := by
  apply Measurable.ite (brownianIntegralGlobalCompatible_measurableSet f)
  · exact brownianIntegralHorizonPath_measurable _ f t
  · exact measurable_const

theorem brownianIntegralGlobalPath_jointlyMeasurable (f : BrownianIntegrand) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianIntegralGlobalPath f p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable (brownianIntegralGlobalPath_continuous f)
    (brownianIntegralGlobalPath_measurable f)

theorem brownianIntegralGlobalPath_integral_ae (f : BrownianIntegrand) (t : ℝ≥0) :
    brownianIntegralGlobalPath f t =ᵐ[brownianDyadicMeasure]
      brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t f := by
  have he : brownianIntegralGlobalPath f t =ᵐ[brownianDyadicMeasure]
      brownianIntegralHorizonPath (brownianIntegralHorizonIndex t) f t :=
    (brownianIntegralGlobalCompatible_ae f).mono (fun _ hω =>
      brownianIntegralGlobalPath_eq_horizon hω _ t (brownianIntegralHorizonIndex_bound t))
  exact he.trans (brownianIntegralHorizonPath_integral_ae _ f t (brownianIntegralHorizonIndex_bound t))

theorem brownianIntegralGlobalPath_martingale_ae (f : BrownianIntegrand) (t : ℝ≥0) :
    brownianIntegralGlobalPath f t =ᵐ[brownianDyadicMeasure] brownianStochasticIntegralProcess f t :=
  (brownianIntegralGlobalPath_integral_ae f t).trans
    (brownianIntegralProcess_ae brownianDyadicPath_isPreBrownianReal f t).symm

theorem brownianIntegralGlobalPath_raw_aestronglyMeasurable (f : BrownianIntegrand) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianNaturalFiltration brownianDyadicPath brownianDyadicPath_measurable t]
      (brownianIntegralGlobalPath f t) brownianDyadicMeasure :=
  (brownianIntegralUpTo_aestronglyMeasurable brownianDyadicPath_isPreBrownianReal t f).congr
    (brownianIntegralGlobalPath_integral_ae f t).symm

end TimeTraps.Probability

end
