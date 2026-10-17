module

public import TimeTraps.Probability.BrownianLocalTimeContinuous

@[expose] public section

/-! A measurable version of the finite-horizon Tanaka candidate with
everywhere continuous paths, nonnegative and nondecreasing on [0,T] and zero at time zero.
It is set to zero outside the proved measurable regular event. Its
fixed-time identification with L² compensation remains almost everywhere;
no occupation-density or support characterization is asserted here. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def brownianLocalTimePath (a : ℝ) (T t : ℝ≥0) (ω : ℕ → ℝ) : ℝ := by
  classical
  exact if brownianLocalTimeRegular a T ω then brownianLocalTimeCandidate a T t ω else 0

theorem brownianLocalTimePath_continuous (a : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Continuous (fun t => brownianLocalTimePath a T t ω) := by
  by_cases hω : brownianLocalTimeRegular a T ω
  · simpa only [brownianLocalTimePath, if_pos hω] using
      brownianLocalTimeCandidate_continuous a T hω.1.continuous
  · simp only [brownianLocalTimePath, if_neg hω]
    exact continuous_const

theorem brownianLocalTimePath_monotoneOn (a : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    MonotoneOn (fun t => brownianLocalTimePath a T t ω) (Icc (0 : ℝ≥0) T) := by
  by_cases hω : brownianLocalTimeRegular a T ω
  · simpa only [brownianLocalTimePath, if_pos hω] using brownianLocalTimeRegular_monotoneOn hω
  · intro s _ t _ _
    simp only [brownianLocalTimePath, if_neg hω, le_refl]

theorem brownianLocalTimePath_nonneg (a : ℝ) {T t : ℝ≥0} (ht : t ≤ T) (ω : ℕ → ℝ) :
    0 ≤ brownianLocalTimePath a T t ω := by
  by_cases hω : brownianLocalTimeRegular a T ω
  · simpa only [brownianLocalTimePath, if_pos hω] using brownianLocalTimeRegular_nonneg hω ht
  · simp only [brownianLocalTimePath, if_neg hω, le_refl]

theorem brownianLocalTimePath_zero (a : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    brownianLocalTimePath a T 0 ω = 0 := by
  by_cases hω : brownianLocalTimeRegular a T ω
  · exact (if_pos hω).trans hω.2.1
  · exact if_neg hω

theorem brownianLocalTimePath_jointlyMeasurable (a : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianLocalTimePath a T p.1 p.2) := by
  apply Measurable.ite ((brownianLocalTimeRegular_measurableSet a T).preimage measurable_snd)
  · exact brownianLocalTimeCandidate_jointlyMeasurable a T
  · exact measurable_const

theorem brownianLocalTimePath_candidate_ae_all (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t,
      brownianLocalTimePath a T t ω = brownianLocalTimeCandidate a T t ω :=
  (brownianLocalTimeRegular_ae a T).mono (fun _ hω _ => if_pos hω)

theorem brownianLocalTimePath_compensation_ae (a : ℝ) {T t : ℝ≥0} (ht : t ≤ T) :
    brownianLocalTimePath a T t =ᵐ[brownianDyadicMeasure]
      brownianTanakaCompensation brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable a t := by
  have he : brownianLocalTimePath a T t =ᵐ[brownianDyadicMeasure] brownianLocalTimeCandidate a T t :=
    (brownianLocalTimePath_candidate_ae_all a T).mono (fun _ hω => hω t)
  exact he.trans (brownianLocalTimeCandidate_compensation_ae a ht)

theorem brownianLocalTimePath_raw_aestronglyMeasurable (a : ℝ) (T t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (brownianLocalTimePath a T t) brownianDyadicMeasure := by
  have he : brownianLocalTimePath a T t =ᵐ[brownianDyadicMeasure] brownianLocalTimeCandidate a T t :=
    (brownianLocalTimePath_candidate_ae_all a T).mono (fun _ hω => hω t)
  exact (brownianLocalTimeCandidate_raw_aestronglyMeasurable a T t).congr he.symm

theorem brownianLocalTimePath_memLp (a : ℝ) {T t : ℝ≥0} (ht : t ≤ T) :
    MemLp (brownianLocalTimePath a T t) 2 brownianDyadicMeasure := by
  have he : brownianLocalTimePath a T t =ᵐ[brownianDyadicMeasure] brownianLocalTimeCandidate a T t :=
    (brownianLocalTimePath_candidate_ae_all a T).mono (fun _ hω => hω t)
  exact (brownianLocalTimeCandidate_memLp a ht).ae_eq he.symm

theorem brownianLocalTimePath_decomposition_ae (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t ≤ T,
      |brownianDyadicPath t ω - a| = |brownianDyadicPath 0 ω - a| +
        brownianSignIntegralPath a T t ω + brownianLocalTimePath a T t ω := by
  filter_upwards [brownianLocalTimePath_candidate_ae_all a T] with ω hω
  intro t _
  rw [hω t]
  unfold brownianLocalTimeCandidate
  ring

end TimeTraps.Probability

end
