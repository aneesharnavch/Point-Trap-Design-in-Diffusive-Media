module

public import TimeTraps.Probability.BrownianSignIntegrandCutoff
public import TimeTraps.Probability.BrownianIntegralContinuousGlobal

@[expose] public section

/-! A continuous version of the sign integral on a fixed finite horizon,
using the constructed Brownian process. It agrees almost everywhere at
each fixed time with the raw-filtration martingale. Raw adaptedness of
this continuous representative is asserted only in the almost-everywhere
strong-measurability sense; the filtration is not completed here. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

def brownianSignIntegralProcess (a : ℝ) (T : ℝ≥0) : ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianStochasticIntegralProcess (brownianDyadicSignIntegrand a T)

theorem brownianSignIntegralProcess_martingale (a : ℝ) (T : ℝ≥0) :
    Martingale (brownianSignIntegralProcess a T) brownianFiltration brownianDyadicMeasure :=
  brownianStochasticIntegralProcess_martingale (brownianDyadicSignIntegrand a T)

def brownianSignIntegralPath (a : ℝ) (T : ℝ≥0) : ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianIntegralGlobalPath (brownianDyadicSignIntegrand a T)

theorem brownianSignIntegralPath_continuous (a : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    Continuous (fun t => brownianSignIntegralPath a T t ω) :=
  brownianIntegralGlobalPath_continuous (brownianDyadicSignIntegrand a T) ω

theorem brownianSignIntegralPath_jointlyMeasurable (a : ℝ) (T : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => brownianSignIntegralPath a T p.1 p.2) :=
  brownianIntegralGlobalPath_jointlyMeasurable (brownianDyadicSignIntegrand a T)

theorem brownianSignIntegralPath_integral_ae (a : ℝ) (T t : ℝ≥0) :
    brownianSignIntegralPath a T t =ᵐ[brownianDyadicMeasure]
      brownianDyadicSignIntegral a (min t T) := by
  have h := brownianIntegralGlobalPath_integral_ae (brownianDyadicSignIntegrand a T) t
  change brownianSignIntegralPath a T t =ᵐ[brownianDyadicMeasure]
    brownianStochasticIntegralUpTo t (brownianDyadicSignIntegrand a T) at h
  rw [brownianDyadicSignIntegral_upTo] at h
  exact h

theorem brownianSignIntegralPath_integral_ae_of_le (a : ℝ) {T t : ℝ≥0} (ht : t ≤ T) :
    brownianSignIntegralPath a T t =ᵐ[brownianDyadicMeasure] brownianDyadicSignIntegral a t := by
  simpa only [min_eq_left ht] using brownianSignIntegralPath_integral_ae a T t

theorem brownianSignIntegralPath_martingale_ae (a : ℝ) (T t : ℝ≥0) :
    brownianSignIntegralPath a T t =ᵐ[brownianDyadicMeasure] brownianSignIntegralProcess a T t :=
  brownianIntegralGlobalPath_martingale_ae (brownianDyadicSignIntegrand a T) t

theorem brownianSignIntegralPath_raw_aestronglyMeasurable (a : ℝ) (T t : ℝ≥0) :
    AEStronglyMeasurable[brownianFiltration t] (brownianSignIntegralPath a T t)
      brownianDyadicMeasure :=
  brownianIntegralGlobalPath_raw_aestronglyMeasurable (brownianDyadicSignIntegrand a T) t

theorem brownianSignIntegralPath_memLp (a : ℝ) (T t : ℝ≥0) :
    MemLp (brownianSignIntegralPath a T t) 2 brownianDyadicMeasure :=
  (Lp.memLp (brownianDyadicSignIntegral a (min t T))).ae_eq
    (brownianSignIntegralPath_integral_ae a T t).symm

theorem brownianSignIntegralPath_condExp (a : ℝ) (T : ℝ≥0) {s t : ℝ≥0} (hst : s ≤ t) :
    brownianDyadicMeasure[brownianSignIntegralPath a T t | brownianFiltration s]
      =ᵐ[brownianDyadicMeasure] brownianSignIntegralPath a T s :=
  (condExp_congr_ae (brownianSignIntegralPath_martingale_ae a T t)).trans
    (((brownianSignIntegralProcess_martingale a T).condExp_ae_eq hst).trans
      (brownianSignIntegralPath_martingale_ae a T s).symm)

end TimeTraps.Probability

end
