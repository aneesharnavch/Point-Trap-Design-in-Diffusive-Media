module

public import TimeTraps.Probability.BrownianIntegralTruncation
public import TimeTraps.Probability.BrownianIntegralMean

@[expose] public section

/-! Raw-filtration measurable representatives of the stochastic integral
up to each time. Their identification with the actual time cutoff is
almost everywhere at each fixed time; no path regularity is asserted. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

def brownianIntegralProcess (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (t : ℝ≥0) : Ω → ℝ :=
  P[brownianIntegral hB f | brownianNaturalFiltration B hBm t]

theorem brownianIntegralProcess_ae (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (t : ℝ≥0) :
    brownianIntegralProcess hB f t =ᵐ[P] brownianIntegralUpTo hB t f :=
  brownianIntegralUpTo_condExp hB t f

theorem brownianIntegralProcess_stronglyAdapted (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) :
    StronglyAdapted (brownianNaturalFiltration B hBm) (brownianIntegralProcess hB f) :=
  fun _ => stronglyMeasurable_condExp

theorem brownianIntegralProcess_martingale (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) :
    Martingale (brownianIntegralProcess hB f) (brownianNaturalFiltration B hBm) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  exact martingale_condExp (brownianIntegral hB f) (brownianNaturalFiltration B hBm) P

theorem brownianIntegralProcess_memLp (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (t : ℝ≥0) :
    MemLp (brownianIntegralProcess hB f t) 2 P :=
  (Lp.memLp (brownianIntegralUpTo hB t f)).ae_eq (brownianIntegralProcess_ae hB f t).symm

theorem brownianIntegralProcess_mean (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (t : ℝ≥0) :
    (∫ ω, brownianIntegralProcess hB f t ω ∂P) = 0 := by
  rw [integral_congr_ae (brownianIntegralProcess_ae hB f t)]
  exact brownianIntegral_mean hB (brownianTimeCutoff B hBm P t f)

theorem brownianIntegralProcess_isometry (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) (t : ℝ≥0) :
    (∫ ω, brownianIntegralProcess hB f t ω ^ 2 ∂P) =
      ∫ p in brownianTimePast t,
        (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2 ∂volume.prod P := by
  calc
    _ = ∫ ω, brownianIntegralUpTo hB t f ω ^ 2 ∂P := by
      apply integral_congr_ae
      filter_upwards [brownianIntegralProcess_ae hB f t] with ω hω
      rw [hω]
    _ = _ := brownianIntegralUpTo_isometry hB t f

theorem brownianIntegralProcess_zero_ae (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) : brownianIntegralProcess hB f 0 =ᵐ[P] 0 := by
  have h := brownianIntegralProcess_ae hB f 0
  rw [brownianIntegralUpTo_zero] at h
  exact h.trans (Lp.coeFn_zero _ _ _)

def brownianStochasticIntegralProcess (f : BrownianIntegrand) :
    ℝ≥0 → (ℕ → ℝ) → ℝ :=
  brownianIntegralProcess brownianDyadicPath_isPreBrownianReal f

theorem brownianStochasticIntegralProcess_martingale (f : BrownianIntegrand) :
    Martingale (brownianStochasticIntegralProcess f) brownianFiltration brownianDyadicMeasure :=
  brownianIntegralProcess_martingale brownianDyadicPath_isPreBrownianReal f

theorem brownianStochasticIntegralProcess_ae (f : BrownianIntegrand) (t : ℝ≥0) :
    brownianStochasticIntegralProcess f t =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralUpTo t f :=
  brownianIntegralProcess_ae brownianDyadicPath_isPreBrownianReal f t

end TimeTraps.Probability

end
