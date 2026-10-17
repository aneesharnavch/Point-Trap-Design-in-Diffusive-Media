module

public import TimeTraps.Probability.BrownianFoldSlopeGlobalCompatibility

@[expose] public section

/-! A concrete all-time continuous normalized fold-slope integral.
Integer horizons are glued on a measurable full-measure event and the
path is zero elsewhere. Equality with the actual L² integral is asserted
at each fixed time; no uncountable intersection of such equalities or
Brownian-law characterization is used. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped NNReal ENNReal Topology

def brownianFoldSlopeGlobalPath (L : ℝ) (hL : 0 < L) (x : ℝ) {σ : ℝ}
    (hσ : 0 < σ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ := by
  classical
  exact if brownianFoldSlopeGlobalCompatible L hL x hσ ω then
    brownianFoldSlopeHorizonPath L hL x hσ (brownianIntegralHorizonIndex t) t ω else 0

theorem brownianFoldSlopeGlobalPath_eq_horizon {L x σ : ℝ} {hL : 0 < L} {hσ : 0 < σ}
    {ω : ℕ → ℝ} (hω : brownianFoldSlopeGlobalCompatible L hL x hσ ω)
    (n : ℕ) (t : ℝ≥0) (ht : t ≤ n) :
    brownianFoldSlopeGlobalPath L hL x hσ t ω = brownianFoldSlopeHorizonPath L hL x hσ n t ω := by
  simp only [brownianFoldSlopeGlobalPath, if_pos hω]
  exact brownianFoldSlopeGlobalCompatible_eq hω (brownianIntegralHorizonIndex t) n t
    (brownianIntegralHorizonIndex_bound t) ht

theorem brownianFoldSlopeGlobalPath_continuous (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (ω : ℕ → ℝ) :
    Continuous (fun t => brownianFoldSlopeGlobalPath L hL x hσ t ω) := by
  by_cases hω : brownianFoldSlopeGlobalCompatible L hL x hσ ω
  · apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt t.val
    have ht : t < (n : ℝ≥0) := by exact_mod_cast hn
    apply (brownianFoldSlopeHorizonPath_continuous L hL x hσ n ω).continuousAt.congr_of_eventuallyEq
    filter_upwards [Iic_mem_nhds ht] with s hs
    exact brownianFoldSlopeGlobalPath_eq_horizon hω n s hs
  · simp only [brownianFoldSlopeGlobalPath, if_neg hω]
    exact continuous_const

theorem brownianFoldSlopeGlobalPath_zero (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (ω : ℕ → ℝ) :
    brownianFoldSlopeGlobalPath L hL x hσ 0 ω = 0 := by
  by_cases hω : brownianFoldSlopeGlobalCompatible L hL x hσ ω
  · exact (brownianFoldSlopeGlobalPath_eq_horizon hω 0 0 (by norm_num)).trans (hω.1 0)
  · simp only [brownianFoldSlopeGlobalPath, if_neg hω]

theorem brownianFoldSlopeGlobalPath_measurable (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    Measurable (brownianFoldSlopeGlobalPath L hL x hσ t) := by
  apply Measurable.ite (brownianFoldSlopeGlobalCompatible_measurableSet L hL x hσ)
  · exact brownianFoldSlopeHorizonPath_measurable L hL x hσ _ t
  · exact measurable_const

theorem brownianFoldSlopeGlobalPath_jointlyMeasurable (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianFoldSlopeGlobalPath L hL x hσ p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable (brownianFoldSlopeGlobalPath_continuous L hL x hσ)
    (brownianFoldSlopeGlobalPath_measurable L hL x hσ)

theorem brownianFoldSlopeGlobalPath_integral_ae (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    brownianFoldSlopeGlobalPath L hL x hσ t =ᵐ[brownianDyadicMeasure]
      brownianDyadicFoldSlopeIntegral L hL x hσ t := by
  have he : brownianFoldSlopeGlobalPath L hL x hσ t =ᵐ[brownianDyadicMeasure]
      brownianFoldSlopeHorizonPath L hL x hσ (brownianIntegralHorizonIndex t) t :=
    (brownianFoldSlopeGlobalCompatible_ae L hL x hσ).mono (fun _ hω =>
      brownianFoldSlopeGlobalPath_eq_horizon hω _ t (brownianIntegralHorizonIndex_bound t))
  have hh := brownianFoldSlopeHorizonPath_integral_ae L hL x hσ (brownianIntegralHorizonIndex t) t
  rw [min_eq_left (brownianIntegralHorizonIndex_bound t)] at hh
  exact he.trans hh

theorem brownianFoldSlopeGlobalPath_memLp (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    MemLp (brownianFoldSlopeGlobalPath L hL x hσ t) 2 brownianDyadicMeasure :=
  (Lp.memLp (brownianDyadicFoldSlopeIntegral L hL x hσ t)).ae_eq
    (brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t).symm

theorem brownianFoldSlopeGlobalPath_toLp (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    (brownianFoldSlopeGlobalPath_memLp L hL x hσ t).toLp
      (brownianFoldSlopeGlobalPath L hL x hσ t) = brownianDyadicFoldSlopeIntegral L hL x hσ t := by
  apply Lp.ext
  exact (brownianFoldSlopeGlobalPath_memLp L hL x hσ t).coeFn_toLp.trans
    (brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t)

theorem brownianFoldSlopeGlobalPath_raw_aestronglyMeasurable (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (brownianFoldSlopeGlobalPath L hL x hσ t)
      brownianDyadicMeasure := by
  have he : brownianFoldSlopeGlobalPath L hL x hσ t =ᵐ[brownianDyadicMeasure]
      brownianFoldSlopeHorizonPath L hL x hσ t t := by
    have hh := brownianFoldSlopeHorizonPath_integral_ae L hL x hσ t t
    rw [min_self] at hh
    exact (brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t).trans hh.symm
  exact (brownianFoldSlopeHorizonPath_raw_aestronglyMeasurable L hL x hσ t t).congr he.symm

theorem brownianFoldSlopeGlobalPath_condExp (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) {s t : ℝ≥0} (hst : s ≤ t) :
    brownianDyadicMeasure[brownianFoldSlopeGlobalPath L hL x hσ t | brownianFiltration s]
      =ᵐ[brownianDyadicMeasure] brownianFoldSlopeGlobalPath L hL x hσ s := by
  have hc := brownianFoldSlopeIntegral_condExp brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL x hσ t s
  rw [min_eq_left hst] at hc
  exact (condExp_congr_ae (brownianFoldSlopeGlobalPath_integral_ae L hL x hσ t)).trans
    (hc.trans (brownianFoldSlopeGlobalPath_integral_ae L hL x hσ s).symm)

theorem brownianFoldSlopeGlobalPath_compact_ae (L : ℝ) (hL : 0 < L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      brownianFoldSlopeGlobalPath L hL x hσ t ω = brownianFoldSlopeHorizonPath L hL x hσ T t ω := by
  have hd : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ k : ℕ,
      brownianFoldSlopeGlobalPath L hL x hσ (denseSeq (BrownianCompactTime T) k).val ω =
        brownianFoldSlopeHorizonPath L hL x hσ T (denseSeq (BrownianCompactTime T) k).val ω := by
    apply ae_all_iff.mpr
    intro k
    have hh := brownianFoldSlopeHorizonPath_integral_ae L hL x hσ T
      (denseSeq (BrownianCompactTime T) k).val
    rw [min_eq_left (denseSeq (BrownianCompactTime T) k).property.2] at hh
    exact (brownianFoldSlopeGlobalPath_integral_ae L hL x hσ _).trans hh.symm
  filter_upwards [hd] with ω hω
  have he := (denseRange_denseSeq (BrownianCompactTime T)).equalizer
    ((brownianFoldSlopeGlobalPath_continuous L hL x hσ ω).comp continuous_subtype_val)
    ((brownianFoldSlopeHorizonPath_continuous L hL x hσ T ω).comp continuous_subtype_val)
    (funext hω)
  intro t ht
  exact congrFun he ⟨t, zero_le, ht⟩

end TimeTraps.Probability

end
