module

public import TimeTraps.Probability.BrownianPredictableDensityFiniteHorizon
public import TimeTraps.Probability.BrownianIntegralMartingale

@[expose] public section

/-! The density theorem feeds arbitrary square-integrable predictable
processes into the already constructed stochastic integral. Its isometry,
zero mean, and martingale process are inherited from that same integral. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}
variable [IsFiniteMeasure P]

noncomputable def brownianPredictableIntegral (hB : IsPreBrownianReal B P)
    (H : ℝ≥0 → Ω → ℝ) (hH : IsStronglyPredictable (brownianNaturalFiltration B hBm) H)
    (T : ℝ≥0) (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod P)) : Lp ℝ 2 P :=
  brownianIntegral hB (brownianPredictableIntegrand H hH T hL)

theorem brownianPredictableIntegral_memLp (hB : IsPreBrownianReal B P)
    (H : ℝ≥0 → Ω → ℝ) (hH : IsStronglyPredictable (brownianNaturalFiltration B hBm) H)
    (T : ℝ≥0) (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod P)) :
    MemLp (brownianPredictableIntegral hB H hH T hL) 2 P := Lp.memLp _

theorem brownianPredictableIntegral_mean (hB : IsPreBrownianReal B P)
    (H : ℝ≥0 → Ω → ℝ) (hH : IsStronglyPredictable (brownianNaturalFiltration B hBm) H)
    (T : ℝ≥0) (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod P)) :
    (∫ ω, brownianPredictableIntegral hB H hH T hL ω ∂P) = 0 :=
  brownianIntegral_mean hB (brownianPredictableIntegrand H hH T hL)

theorem brownianPredictableIntegral_isometry (hB : IsPreBrownianReal B P)
    (H : ℝ≥0 → Ω → ℝ) (hH : IsStronglyPredictable (brownianNaturalFiltration B hBm) H)
    (T : ℝ≥0) (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod P)) :
    (∫ ω, brownianPredictableIntegral hB H hH T hL ω ^ 2 ∂P) =
      ∫ p, brownianSquareProcess H T p ^ 2 ∂volume.prod P := by
  exact (brownianIntegral_isometry hB (brownianPredictableIntegrand H hH T hL)).trans
    (integral_congr_ae ((brownianPredictableIntegrand_coe H hH T hL).pow_const 2))

theorem brownianPredictableIntegral_martingale (hB : IsPreBrownianReal B P)
    (H : ℝ≥0 → Ω → ℝ) (hH : IsStronglyPredictable (brownianNaturalFiltration B hBm) H)
    (T : ℝ≥0) (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod P)) :
    Martingale
      (brownianIntegralProcess hB (brownianPredictableIntegrand H hH T hL))
      (brownianNaturalFiltration B hBm) P :=
  brownianIntegralProcess_martingale hB (brownianPredictableIntegrand H hH T hL)

noncomputable def brownianPredictableStochasticIntegrand (H : ℝ≥0 → (ℕ → ℝ) → ℝ)
    (hH : IsStronglyPredictable brownianFiltration H) (T : ℝ≥0)
    (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod brownianDyadicMeasure)) :
    BrownianIntegrand := brownianPredictableIntegrand H hH T hL

noncomputable def brownianPredictableStochasticIntegral (H : ℝ≥0 → (ℕ → ℝ) → ℝ)
    (hH : IsStronglyPredictable brownianFiltration H) (T : ℝ≥0)
    (hL : MemLp (brownianSquareProcess H T) 2 (volume.prod brownianDyadicMeasure)) :
    Lp ℝ 2 brownianDyadicMeasure :=
  brownianStochasticIntegral (brownianPredictableStochasticIntegrand H hH T hL)

end TimeTraps.Probability
