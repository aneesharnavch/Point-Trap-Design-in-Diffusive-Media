module

public import TimeTraps.Probability.BrownianLocalTimeGlobal

@[expose] public section

/-! A consistent continuous global sign integral on the same regular
event as the global Tanaka candidate. It agrees with every finite-horizon
sign version on its compact interval almost surely, and the real path
decomposition then holds simultaneously at all nonnegative times. No
spatial regularity, occupation identity, or completed filtration is used. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def brownianSignIntegralGlobalPath (a : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ := by
  classical
  exact if brownianLocalTimeGlobalRegular a ω then
    |brownianDyadicPath t ω - a| - |brownianDyadicPath 0 ω - a| -
      brownianLocalTimeGlobalPath a t ω else 0

theorem brownianSignIntegralGlobalPath_eq_horizon {a : ℝ} {ω : ℕ → ℝ}
    (hω : brownianLocalTimeGlobalRegular a ω) (n : ℕ) (t : ℝ≥0) (ht : t ≤ n) :
    brownianSignIntegralGlobalPath a t ω = brownianSignIntegralPath a n t ω := by
  rw [brownianSignIntegralGlobalPath, if_pos hω,
    brownianLocalTimeGlobalPath_eq_horizon hω n t ht,
    brownianLocalTimePath, if_pos (hω.1 n)]
  unfold brownianLocalTimeCandidate
  ring

theorem brownianSignIntegralGlobalPath_continuous (a : ℝ) (ω : ℕ → ℝ) :
    Continuous (fun t => brownianSignIntegralGlobalPath a t ω) := by
  by_cases hω : brownianLocalTimeGlobalRegular a ω
  · simp only [brownianSignIntegralGlobalPath, if_pos hω]
    exact (((hω.1 0).1.continuous.sub continuous_const).abs.sub continuous_const).sub
      (brownianLocalTimeGlobalPath_continuous a ω)
  · simp only [brownianSignIntegralGlobalPath, if_neg hω]
    exact continuous_const

theorem brownianSignIntegralGlobalPath_zero (a : ℝ) (ω : ℕ → ℝ) :
    brownianSignIntegralGlobalPath a 0 ω = 0 := by
  simp only [brownianSignIntegralGlobalPath, brownianLocalTimeGlobalPath_zero, sub_self, ite_self]

theorem brownianSignIntegralGlobalPath_jointlyMeasurable (a : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianSignIntegralGlobalPath a p.1 p.2) := by
  apply Measurable.ite ((brownianLocalTimeGlobalRegular_measurableSet a).preimage measurable_snd)
  · exact ((brownianDyadicPath_jointly_measurable.sub_const a).abs.sub
      (((brownianDyadicPath_measurable 0).comp measurable_snd).sub_const a).abs).sub
        (brownianLocalTimeGlobalPath_jointlyMeasurable a)
  · exact measurable_const

theorem brownianSignIntegralGlobalPath_compact_ae (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      brownianSignIntegralGlobalPath a t ω = brownianSignIntegralPath a T t ω := by
  filter_upwards [brownianLocalTimeGlobalRegular_ae a, brownianLocalTimeRegular_ae a T,
    brownianLocalTimeGlobalPath_compact_ae a T] with ω hg hr he
  intro t ht
  rw [brownianSignIntegralGlobalPath, if_pos hg, he t ht, brownianLocalTimePath, if_pos hr]
  unfold brownianLocalTimeCandidate
  ring

theorem brownianSignIntegralGlobalPath_integral_ae (a : ℝ) (t : ℝ≥0) :
    brownianSignIntegralGlobalPath a t =ᵐ[brownianDyadicMeasure] brownianDyadicSignIntegral a t := by
  have he : brownianSignIntegralGlobalPath a t =ᵐ[brownianDyadicMeasure] brownianSignIntegralPath a t t :=
    (brownianSignIntegralGlobalPath_compact_ae a t).mono (fun _ hω => hω t le_rfl)
  exact he.trans (brownianSignIntegralPath_integral_ae_of_le a le_rfl)

theorem brownianSignIntegralGlobalPath_memLp (a : ℝ) (t : ℝ≥0) :
    MemLp (brownianSignIntegralGlobalPath a t) 2 brownianDyadicMeasure :=
  (Lp.memLp (brownianDyadicSignIntegral a t)).ae_eq (brownianSignIntegralGlobalPath_integral_ae a t).symm

theorem brownianSignIntegralGlobalPath_raw_aestronglyMeasurable (a : ℝ) (t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (brownianSignIntegralGlobalPath a t) brownianDyadicMeasure := by
  have he : brownianSignIntegralGlobalPath a t =ᵐ[brownianDyadicMeasure] brownianSignIntegralPath a t t :=
    (brownianSignIntegralGlobalPath_compact_ae a t).mono (fun _ hω => hω t le_rfl)
  exact (brownianSignIntegralPath_raw_aestronglyMeasurable a t t).congr he.symm

theorem brownianSignIntegralGlobalPath_condExp (a : ℝ) {s t : ℝ≥0} (hst : s ≤ t) :
    brownianDyadicMeasure[brownianSignIntegralGlobalPath a t | brownianFiltration s]
      =ᵐ[brownianDyadicMeasure] brownianSignIntegralGlobalPath a s := by
  have hc := brownianSignIntegral_condExp brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a t s
  rw [min_eq_left hst] at hc
  exact (condExp_congr_ae (brownianSignIntegralGlobalPath_integral_ae a t)).trans
    (hc.trans (brownianSignIntegralGlobalPath_integral_ae a s).symm)

theorem brownianLocalTimeGlobalPath_decomposition_ae (a : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      |brownianDyadicPath t ω - a| = |brownianDyadicPath 0 ω - a| +
        brownianSignIntegralGlobalPath a t ω + brownianLocalTimeGlobalPath a t ω := by
  filter_upwards [brownianLocalTimeGlobalRegular_ae a] with ω hω
  intro t
  rw [brownianSignIntegralGlobalPath, if_pos hω]
  ring

end TimeTraps.Probability

end
