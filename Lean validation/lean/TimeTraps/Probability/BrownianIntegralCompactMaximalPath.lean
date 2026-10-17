module

public import TimeTraps.Probability.BrownianIntegralElementaryPathSum
public import TimeTraps.Probability.BrownianIntegralMaximal
public import Mathlib.Topology.ContinuousMap.Compact
public import Mathlib.Topology.ContinuousMap.SecondCountableSpace

@[expose] public section

/-! A continuous representative on every sample, obtained by setting the
finite elementary-sum path to zero off the proved measurable regularity
event. On that one full-measure event it agrees at every time with the
original explicit path. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

abbrev BrownianDyadicElementary :=
  BrownianIntegralElementary brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure

abbrev BrownianCompactTime (T : ℝ≥0) := Icc (0 : ℝ≥0) T

instance brownianCompactTime_nonempty (T : ℝ≥0) : Nonempty (BrownianCompactTime T) :=
  ⟨⟨0, by simp⟩⟩

instance brownianCompactTime_compactSpace (T : ℝ≥0) : CompactSpace (BrownianCompactTime T) :=
  isCompact_iff_compactSpace.mp isCompact_Icc

theorem brownianDyadicRegular_measurableSet : MeasurableSet {ω : ℕ → ℝ | BrownianDyadicRegular ω} := by
  have he : {ω : ℕ → ℝ | BrownianDyadicRegular ω} =
      {ω | (∀ i j, brownianDyadicTime i = brownianDyadicTime j → ω i = ω j) ∧
        ∀ R : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k < R * 64 ^ n,
          |ω (Nat.pair n (k + 1)) - ω (Nat.pair n k)| < (1 / 2 : ℝ) ^ n} := by
    ext ω
    exact ⟨fun h => ⟨h.consistent, h.increments⟩, fun h => ⟨h.1, h.2⟩⟩
  rw [he]
  measurability

variable {I : Type*} [Fintype I]

def brownianElementaryRegularPath (a : I → BrownianDyadicElementary)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ := by
  classical
  exact if BrownianDyadicRegular ω then brownianElementarySumPath a t ω else 0

theorem brownianElementaryRegularPath_continuous (a : I → BrownianDyadicElementary)
    (ω : ℕ → ℝ) : Continuous (fun t => brownianElementaryRegularPath a t ω) := by
  by_cases hω : BrownianDyadicRegular ω
  · simpa only [brownianElementaryRegularPath, if_pos hω] using
      brownianElementarySumPath_continuous a hω.continuous
  · simp only [brownianElementaryRegularPath, if_neg hω]
    exact continuous_const

theorem brownianElementaryRegularPath_measurable (a : I → BrownianDyadicElementary)
    (t : ℝ≥0) : Measurable (brownianElementaryRegularPath a t) := by
  apply Measurable.ite brownianDyadicRegular_measurableSet
  · exact (brownianDyadicElementarySumPath_jointly_measurable a).comp
      (measurable_const.prodMk measurable_id)
  · exact measurable_const

theorem brownianElementaryRegularPath_ae_all (a : I → BrownianDyadicElementary) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t,
      brownianElementaryRegularPath a t ω = brownianElementarySumPath a t ω :=
  brownianDyadic_regular_ae.mono (fun _ hω _ => if_pos hω)

theorem brownianElementaryRegularPath_martingale_ae (a : I → BrownianDyadicElementary) (t : ℝ≥0) :
    brownianElementaryRegularPath a t =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralProcess (brownianElementarySumIntegrand a) t := by
  have ha : brownianElementaryRegularPath a t =ᵐ[brownianDyadicMeasure]
      brownianElementarySumPath a t :=
    (brownianElementaryRegularPath_ae_all a).mono (fun _ hω => hω t)
  exact ha.trans (brownianElementarySumPath_martingale_ae brownianDyadicPath_isPreBrownianReal a t)

def brownianElementaryCompactPath (a : I → BrownianDyadicElementary) (T : ℝ≥0)
    (ω : ℕ → ℝ) : C(BrownianCompactTime T, ℝ) :=
  ⟨fun t => brownianElementaryRegularPath a t.val ω,
    (brownianElementaryRegularPath_continuous a ω).comp continuous_subtype_val⟩

def brownianElementaryCompactMax (a : I → BrownianDyadicElementary) (T : ℝ≥0)
    (ω : ℕ → ℝ) : ℝ := ‖brownianElementaryCompactPath a T ω‖

theorem brownianElementaryCompactMax_eq_sup (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) (ω : ℕ → ℝ) :
    brownianElementaryCompactMax a T ω =
      ⨆ t : BrownianCompactTime T, |brownianElementaryRegularPath a t.val ω| := by
  exact (brownianElementaryCompactPath a T ω).norm_eq_iSup_norm.trans
    (by simp only [Real.norm_eq_abs]; rfl)

theorem brownianElementaryCompactMax_eq_original_sup_ae (a : I → BrownianDyadicElementary)
    (T : ℝ≥0) : brownianElementaryCompactMax a T =ᵐ[brownianDyadicMeasure]
      (fun ω => ⨆ t : BrownianCompactTime T, |brownianElementarySumPath a t.val ω|) := by
  filter_upwards [brownianElementaryRegularPath_ae_all a] with ω hω
  rw [brownianElementaryCompactMax_eq_sup]
  congr 1
  funext t
  rw [hω]

end TimeTraps.Probability

end
