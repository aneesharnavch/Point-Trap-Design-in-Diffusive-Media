module

public import TimeTraps.Probability.BrownianIntegralTruncationAlgebra

@[expose] public section

/-! The stochastic integral up to a deterministic time is defined by
integrating the actual truncated product-L² integrand. Its isometry and
conditional-expectation identity follow from the past/future decomposition. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
variable {B : ℝ≥0 → Ω → ℝ} {hBm : ∀ t, Measurable (B t)} {P : Measure Ω}

def brownianIntegralUpTo (hB : IsPreBrownianReal B P) (t : ℝ≥0) :
    brownianIntegralSpace B hBm P →L[ℝ] Lp ℝ 2 P :=
  (brownianIntegral hB).toContinuousLinearMap.comp (brownianTimeCutoff B hBm P t)

theorem brownianIntegralUpTo_norm_le (hB : IsPreBrownianReal B P) (t : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) : ‖brownianIntegralUpTo hB t f‖ ≤ ‖f‖ := by
  change ‖brownianIntegral hB (brownianTimeCutoff B hBm P t f)‖ ≤ ‖f‖
  rw [(brownianIntegral hB).norm_map]
  exact brownianTimeCutoff_norm_le t f

theorem brownianIntegralUpTo_isometry (hB : IsPreBrownianReal B P) (t : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) :
    (∫ ω, brownianIntegralUpTo hB t f ω ^ 2 ∂P) =
      ∫ p in brownianTimePast t, (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2 ∂volume.prod P := by
  calc
    _ = ∫ p, (brownianTimeCutoff B hBm P t f :
        Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2 ∂volume.prod P :=
      brownianIntegral_isometry hB _
    _ = ∫ p, ((brownianTimePast t).indicator
        (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p) ^ 2 ∂volume.prod P :=
      integral_congr_ae ((brownianTimeCutoff_coe t f).pow_const 2)
    _ = ∫ p, (brownianTimePast t).indicator
        (fun p => (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p ^ 2) p ∂volume.prod P := by
      apply integral_congr_ae
      filter_upwards [] with p
      by_cases hp : p ∈ brownianTimePast t <;> simp [hp]
    _ = _ := integral_indicator (brownianTimePast_measurable t)

theorem brownianIntegralUpTo_aestronglyMeasurable (hB : IsPreBrownianReal B P) (t : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) :
    AEStronglyMeasurable[brownianNaturalFiltration B hBm t] (brownianIntegralUpTo hB t f) P :=
  brownianIntegral_aestronglyMeasurable_past hB t _ (brownianTimeCutoff_mem_past t f)

theorem brownianIntegralUpTo_condExp (hB : IsPreBrownianReal B P) (t : ℝ≥0)
    (f : brownianIntegralSpace B hBm P) :
    P[brownianIntegral hB f | brownianNaturalFiltration B hBm t] =ᵐ[P] brownianIntegralUpTo hB t f := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let g := brownianTimeCutoff B hBm P t f
  have htail := brownianIntegral_condExp_future hB t (f - g) (brownianTimeCutoff_sub_mem_future t f)
  have hrep : brownianIntegral hB (f - g) =ᵐ[P]
      (fun ω => brownianIntegral hB f ω - brownianIntegral hB g ω) := by
    rw [map_sub]
    exact Lp.coeFn_sub _ _
  have hz : P[fun ω => brownianIntegral hB f ω - brownianIntegral hB g ω |
      brownianNaturalFiltration B hBm t] =ᵐ[P] 0 :=
    (condExp_congr_ae hrep).symm.trans htail
  have hsub := condExp_sub ((Lp.memLp (brownianIntegral hB f)).integrable (by norm_num))
    ((Lp.memLp (brownianIntegral hB g)).integrable (by norm_num)) (brownianNaturalFiltration B hBm t)
  have hpast := brownianIntegral_condExp_past hB t g (brownianTimeCutoff_mem_past t f)
  filter_upwards [hz, hsub, hpast] with ω hzero hsplit hp
  change P[brownianIntegral hB f | brownianNaturalFiltration B hBm t] ω =
    brownianIntegral hB g ω
  change P[fun ω => brownianIntegral hB f ω - brownianIntegral hB g ω |
    brownianNaturalFiltration B hBm t] ω = 0 at hzero
  change P[fun ω => brownianIntegral hB f ω - brownianIntegral hB g ω |
    brownianNaturalFiltration B hBm t] ω =
    P[brownianIntegral hB f | brownianNaturalFiltration B hBm t] ω -
      P[brownianIntegral hB g | brownianNaturalFiltration B hBm t] ω at hsplit
  rw [hp] at hsplit
  exact sub_eq_zero.mp (hsplit.symm.trans hzero)

theorem brownianIntegralUpTo_zero (hB : IsPreBrownianReal B P)
    (f : brownianIntegralSpace B hBm P) : brownianIntegralUpTo hB 0 f = 0 := by
  change brownianIntegral hB (brownianTimeCutoff B hBm P 0 f) = 0
  rw [brownianTimeCutoff_zero, map_zero]

def brownianStochasticIntegralUpTo (t : ℝ≥0) : BrownianIntegrand →L[ℝ] Lp ℝ 2 brownianDyadicMeasure :=
  brownianIntegralUpTo brownianDyadicPath_isPreBrownianReal t

theorem brownianStochasticIntegralUpTo_condExp (t : ℝ≥0) (f : BrownianIntegrand) :
    brownianDyadicMeasure[brownianStochasticIntegral f | brownianFiltration t] =ᵐ[brownianDyadicMeasure]
      brownianStochasticIntegralUpTo t f :=
  brownianIntegralUpTo_condExp brownianDyadicPath_isPreBrownianReal t f

end TimeTraps.Probability

end
