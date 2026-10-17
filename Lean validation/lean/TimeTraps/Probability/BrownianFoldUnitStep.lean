module

public import TimeTraps.Analysis.ReflectedFoldUnitSlope
public import TimeTraps.Probability.BrownianFoldSlopeTimeGrid
public import TimeTraps.Probability.BrownianIntegralPartition

@[expose] public section

/-! Actual predictable finite step integrands with unit-valued fold
coefficients, including the coefficient at time zero. Their completed
stochastic integrals are the literal finite Brownian increment sums. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def brownianFoldUnitCoefficient (B : ℝ≥0 → Ω → ℝ) (L x σ : ℝ) (T : ℝ≥0)
    (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) : ℝ :=
  reflectedFoldUnitSlope L (x + σ * B (brownianDyadicGrid T n i.castSucc) ω)

theorem brownianFoldUnitCoefficient_adapted (hBm : ∀ t, Measurable (B t))
    (L : ℝ) (hL : 0 < L) (x σ : ℝ) (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) :
    StronglyMeasurable[brownianNaturalFiltration B hBm (brownianDyadicGrid T n i.castSucc)]
      (brownianFoldUnitCoefficient B L x σ T n i) :=
  ((reflectedFoldUnitSlope_measurable L hL).comp
    (measurable_const.add (measurable_const.mul
      (brownianNaturalFiltration_stronglyAdapted B hBm _).measurable))).stronglyMeasurable

theorem brownianFoldUnitCoefficient_abs (B : ℝ≥0 → Ω → ℝ) (L : ℝ) (hL : 0 < L)
    (x σ : ℝ) (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) (ω : Ω) :
    |brownianFoldUnitCoefficient B L x σ T n i ω| = 1 :=
  reflectedFoldUnitSlope_abs L hL _

theorem brownianFoldUnitCoefficient_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) :
    MemLp (brownianFoldUnitCoefficient B L x σ T n i) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hm : Measurable (brownianFoldUnitCoefficient B L x σ T n i) :=
    (reflectedFoldUnitSlope_measurable L hL).comp
      (measurable_const.add (measurable_const.mul (hBm _)))
  apply (memLp_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  filter_upwards [] with ω
  exact (brownianFoldUnitCoefficient_abs B L hL x σ T n i ω).le

def brownianFoldUnitElementary (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) : BrownianIntegralElementary B hBm P where
  left := brownianDyadicGrid T n i.castSucc
  right := brownianDyadicGrid T n i.succ
  ordered := brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i)
  coefficient := brownianFoldUnitCoefficient B L x σ T n i
  adapted := brownianFoldUnitCoefficient_adapted hBm L hL x σ T n i
  squareIntegrable := brownianFoldUnitCoefficient_memLp hB hBm L hL x σ T n i

def brownianFoldUnitStepIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (T : ℝ≥0) (n : ℕ) : brownianIntegralSpace B hBm P :=
  brownianElementarySumIntegrand (brownianFoldUnitElementary hB hBm L hL x σ T n)

def brownianFoldUnitTimeGrid (B : ℝ≥0 → Ω → ℝ) (L x σ : ℝ) (T : ℝ≥0) (n : ℕ) : ℝ × Ω → ℝ :=
  brownianSquareStepProcess (fun t ω => reflectedFoldUnitSlope L (x + σ * B t ω)) T n

theorem brownianFoldUnitStepIntegrand_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (T : ℝ≥0) (n : ℕ) :
    (brownianFoldUnitStepIntegrand hB hBm L hL x σ T n : Lp ℝ 2 ((volume : Measure ℝ).prod P))
      =ᵐ[volume.prod P] brownianFoldUnitTimeGrid B L x σ T n :=
  brownianElementarySumIntegrand_coe (brownianFoldUnitElementary hB hBm L hL x σ T n)

theorem brownianFoldUnitTimeGrid_predictable (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (T : ℝ≥0) (n : ℕ) :
    IsStronglyPredictable (brownianNaturalFiltration B hBm)
      (fun t ω => brownianFoldUnitTimeGrid B L x σ T n (t.val, ω)) :=
  brownianElementarySum_predictable (brownianFoldUnitElementary hB hBm L hL x σ T n)

theorem brownianFoldUnitStep_integral_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (x σ : ℝ)
    (T : ℝ≥0) (n : ℕ) :
    brownianIntegral hB (brownianFoldUnitStepIntegrand hB hBm L hL x σ T n) =ᵐ[P]
      brownianStepIntegral B (brownianDyadicGrid T n) (brownianFoldUnitCoefficient B L x σ T n) :=
  brownianIntegral_elementarySum_ae hB (brownianFoldUnitElementary hB hBm L hL x σ T n)

end TimeTraps.Probability

end
