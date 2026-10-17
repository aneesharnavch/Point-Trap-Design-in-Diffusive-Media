module

public import TimeTraps.Probability.BrownianAdaptedContinuousProcess
public import TimeTraps.Probability.BrownianIntegralPartition

@[expose] public section

/-! Actual elementary Brownian integrands for bounded processes adapted
to the original raw Brownian natural filtration. The coefficients are
their left dyadic values, and the completed integrals are the literal
finite Brownian increment sums. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B H : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {M : ℝ≥0}

theorem brownianAdaptedContinuous_coefficient_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (t : ℝ≥0) : MemLp (H t) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply (memLp_const M.val).mono'
    ((hH t).mono ((brownianNaturalFiltration B hBm).le t)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => hb t ω)

def brownianAdaptedContinuousElementary (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) :
    BrownianIntegralElementary B hBm P where
  left := brownianDyadicGrid T n i.castSucc
  right := brownianDyadicGrid T n i.succ
  ordered := brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i)
  coefficient := H (brownianDyadicGrid T n i.castSucc)
  adapted := hH _
  squareIntegrable := brownianAdaptedContinuous_coefficient_memLp hB hBm hH hb _

def brownianAdaptedContinuousStepIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ) : brownianIntegralSpace B hBm P :=
  brownianElementarySumIntegrand (brownianAdaptedContinuousElementary hB hBm hH hb T n)

theorem brownianAdaptedContinuousStepIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ) :
    (brownianAdaptedContinuousStepIntegrand hB hBm hH hb T n :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] brownianSquareStepProcess H T n :=
  brownianElementarySumIntegrand_coe (brownianAdaptedContinuousElementary hB hBm hH hb T n)

theorem brownianAdaptedContinuousStep_predictable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ) :
    IsStronglyPredictable (brownianNaturalFiltration B hBm)
      (fun t ω => brownianSquareStepProcess H T n (t.val, ω)) :=
  brownianElementarySum_predictable (brownianAdaptedContinuousElementary hB hBm hH hb T n)

theorem brownianAdaptedContinuousStep_integral_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hH : ∀ t, StronglyMeasurable[brownianNaturalFiltration B hBm t] (H t))
    (hb : ∀ t ω, |H t ω| ≤ M.val) (T : ℝ≥0) (n : ℕ) :
    brownianIntegral hB (brownianAdaptedContinuousStepIntegrand hB hBm hH hb T n) =ᵐ[P]
      brownianStepIntegral B (brownianDyadicGrid T n)
        (fun i => H (brownianDyadicGrid T n i.castSucc)) :=
  brownianIntegral_elementarySum_ae hB (brownianAdaptedContinuousElementary hB hBm hH hb T n)

end TimeTraps.Probability

end
