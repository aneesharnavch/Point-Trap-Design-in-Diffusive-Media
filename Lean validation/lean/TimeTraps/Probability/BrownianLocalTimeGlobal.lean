module

public import TimeTraps.Probability.BrownianLocalTimeGlobalCompatibility

@[expose] public section

/-! Integer horizons give one global Tanaka candidate at each fixed
level. The process is zero off the proved common regular event, and has
everywhere continuous, nonnegative, nondecreasing paths starting at zero.
Its actual L² compensation and raw-filtration identities are fixed-time
almost-everywhere statements. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

def brownianLocalTimeGlobalPath (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ := by
  classical
  exact if brownianLocalTimeGlobalRegular a ω then
    brownianLocalTimePath a (brownianIntegralHorizonIndex t) t ω else 0

theorem brownianLocalTimeGlobalPath_eq_horizon {a : ℝ} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeGlobalRegular a ω) (n : ℕ) (t : ℝ≥0) (ht : t ≤ n) :
    brownianLocalTimeGlobalPath a t ω = brownianLocalTimePath a n t ω := by
  simp only [brownianLocalTimeGlobalPath, if_pos hω]
  exact brownianLocalTimeGlobalRegular_eq hω (brownianIntegralHorizonIndex t) n t
    (brownianIntegralHorizonIndex_bound t) ht

theorem brownianLocalTimeGlobalPath_continuous (a : ℝ) (ω : ℕ → ℝ) :
    Continuous (fun t => brownianLocalTimeGlobalPath a t ω) := by
  by_cases hω : brownianLocalTimeGlobalRegular a ω
  · apply continuous_iff_continuousAt.mpr
    intro t
    obtain ⟨n, hn⟩ := exists_nat_gt t.val
    have ht : t < (n : ℝ≥0) := by exact_mod_cast hn
    apply (brownianLocalTimePath_continuous a n ω).continuousAt.congr_of_eventuallyEq
    filter_upwards [Iic_mem_nhds ht] with s hs
    exact brownianLocalTimeGlobalPath_eq_horizon hω n s hs
  · simp only [brownianLocalTimeGlobalPath, if_neg hω]
    exact continuous_const

theorem brownianLocalTimeGlobalPath_monotone (a : ℝ) (ω : ℕ → ℝ) :
    Monotone (fun t => brownianLocalTimeGlobalPath a t ω) := by
  intro s t hst
  change brownianLocalTimeGlobalPath a s ω ≤ brownianLocalTimeGlobalPath a t ω
  by_cases hω : brownianLocalTimeGlobalRegular a ω
  · let n := brownianIntegralHorizonIndex t
    have ht : t ≤ (n : ℝ≥0) := brownianIntegralHorizonIndex_bound t
    rw [brownianLocalTimeGlobalPath_eq_horizon hω n s (hst.trans ht),
      brownianLocalTimeGlobalPath_eq_horizon hω n t ht]
    exact brownianLocalTimePath_monotoneOn a n ω ⟨zero_le, hst.trans ht⟩ ⟨zero_le, ht⟩ hst
  · simp only [brownianLocalTimeGlobalPath, if_neg hω, le_refl]

theorem brownianLocalTimeGlobalPath_zero (a : ℝ) (ω : ℕ → ℝ) :
    brownianLocalTimeGlobalPath a 0 ω = 0 := by
  by_cases hω : brownianLocalTimeGlobalRegular a ω
  · rw [brownianLocalTimeGlobalPath, if_pos hω]
    exact brownianLocalTimePath_zero a _ ω
  · exact if_neg hω

theorem brownianLocalTimeGlobalPath_nonneg (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    0 ≤ brownianLocalTimeGlobalPath a t ω := by
  have h := brownianLocalTimeGlobalPath_monotone a ω (zero_le : (0 : ℝ≥0) ≤ t)
  change brownianLocalTimeGlobalPath a 0 ω ≤ brownianLocalTimeGlobalPath a t ω at h
  rw [brownianLocalTimeGlobalPath_zero] at h
  exact h

theorem brownianLocalTimeGlobalPath_measurable (a : ℝ) (t : ℝ≥0) :
    Measurable (brownianLocalTimeGlobalPath a t) := by
  apply Measurable.ite (brownianLocalTimeGlobalRegular_measurableSet a)
  · exact brownianLocalTimePath_measurable a _ t
  · exact measurable_const

theorem brownianLocalTimeGlobalPath_jointlyMeasurable (a : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianLocalTimeGlobalPath a p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable (brownianLocalTimeGlobalPath_continuous a)
    (brownianLocalTimeGlobalPath_measurable a)

theorem brownianLocalTimeGlobalPath_compact_ae (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      brownianLocalTimeGlobalPath a t ω = brownianLocalTimePath a T t ω := by
  let n := brownianIntegralHorizonIndex T
  have hT : T ≤ (n : ℝ≥0) := brownianIntegralHorizonIndex_bound T
  filter_upwards [brownianLocalTimeGlobalRegular_ae a, brownianLocalTimePath_horizon_ae a n T]
    with ω hω he
  intro t ht
  exact (brownianLocalTimeGlobalPath_eq_horizon hω n t (ht.trans hT)).trans
    (he t (le_min (ht.trans hT) ht))

theorem brownianLocalTimeGlobalPath_compensation_ae (a : ℝ) (t : ℝ≥0) :
    brownianLocalTimeGlobalPath a t =ᵐ[brownianDyadicMeasure]
      brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable a t := by
  have he : brownianLocalTimeGlobalPath a t =ᵐ[brownianDyadicMeasure] brownianLocalTimePath a t t :=
    (brownianLocalTimeGlobalPath_compact_ae a t).mono (fun _ hω => hω t le_rfl)
  exact he.trans (brownianLocalTimePath_compensation_ae a le_rfl)

theorem brownianLocalTimeGlobalPath_memLp (a : ℝ) (t : ℝ≥0) :
    MemLp (brownianLocalTimeGlobalPath a t) 2 brownianDyadicMeasure :=
  (Lp.memLp (brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a t)).ae_eq (brownianLocalTimeGlobalPath_compensation_ae a t).symm

theorem brownianLocalTimeGlobalPath_raw_aestronglyMeasurable (a : ℝ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (brownianLocalTimeGlobalPath a t) brownianDyadicMeasure := by
  have he : brownianLocalTimeGlobalPath a t =ᵐ[brownianDyadicMeasure] brownianLocalTimePath a t t :=
    (brownianLocalTimeGlobalPath_compact_ae a t).mono (fun _ hω => hω t le_rfl)
  exact (brownianLocalTimePath_raw_aestronglyMeasurable a t t).congr he.symm

end TimeTraps.Probability

end
