module

public import TimeTraps.Probability.BrownianSignIntegrandStochastic
public import TimeTraps.Probability.BrownianIntegralTruncation

@[expose] public section

/-! Time cutoff of the actual completed sign integrand is exactly the
sign integrand on the shorter horizon. Consequently its integral up to
a time and its raw conditional expectation have the same identification. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianSignIntegrand_cutoff (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T t : ℝ≥0) :
    brownianTimeCutoff B hBm P t (brownianSignIntegrand hB hBm hjoint a T) =
      brownianSignIntegrand hB hBm hjoint a (min t T) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [brownianTimeCutoff_coe t (brownianSignIntegrand hB hBm hjoint a T),
    brownianSignIntegrand_coe hB hBm hjoint a T,
    brownianSignIntegrand_coe hB hBm hjoint a (min t T)] with p hcut hT hmin
  rw [hcut, hmin]
  by_cases ht : p.1 ≤ t.val
  · have hp : p ∈ brownianTimePast t := ht
    rw [indicator_of_mem hp, hT]
    have hle : p.1 ≤ (min t T).val ↔ p.1 ≤ T.val := by
      change p.1 ≤ min t.val T.val ↔ p.1 ≤ T.val
      simp only [le_min_iff, ht, true_and]
    simp only [indicator_apply, mem_Ioc, hle]
  · have hp : p ∉ brownianTimePast t := ht
    rw [indicator_of_notMem hp]
    have hn : p.1 ∉ Ioc (0 : ℝ) (min t T).val := by
      intro h
      exact ht (h.2.trans (min_le_left t.val T.val))
    rw [indicator_of_notMem hn, zero_mul]

theorem brownianSignIntegral_upTo (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T t : ℝ≥0) :
    brownianIntegralUpTo hB t (brownianSignIntegrand hB hBm hjoint a T) =
      brownianSignIntegral hB hBm hjoint a (min t T) := by
  change brownianIntegral hB (brownianTimeCutoff B hBm P t
    (brownianSignIntegrand hB hBm hjoint a T)) = _
  rw [brownianSignIntegrand_cutoff]
  rfl

theorem brownianSignIntegral_upTo_of_le (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ)
    {T t : ℝ≥0} (ht : t ≤ T) :
    brownianIntegralUpTo hB t (brownianSignIntegrand hB hBm hjoint a T) =
      brownianSignIntegral hB hBm hjoint a t := by
  rw [brownianSignIntegral_upTo, min_eq_left ht]

theorem brownianSignIntegral_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T t : ℝ≥0) :
    P[brownianSignIntegral hB hBm hjoint a T | brownianNaturalFiltration B hBm t] =ᵐ[P]
      brownianSignIntegral hB hBm hjoint a (min t T) := by
  have h := brownianIntegralUpTo_condExp hB t (brownianSignIntegrand hB hBm hjoint a T)
  rw [brownianSignIntegral_upTo] at h
  exact h

theorem brownianDyadicSignIntegrand_cutoff (a : ℝ) (T t : ℝ≥0) :
    brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure t
        (brownianDyadicSignIntegrand a T) = brownianDyadicSignIntegrand a (min t T) :=
  brownianSignIntegrand_cutoff brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a T t

theorem brownianDyadicSignIntegral_upTo (a : ℝ) (T t : ℝ≥0) :
    brownianStochasticIntegralUpTo t (brownianDyadicSignIntegrand a T) =
      brownianDyadicSignIntegral a (min t T) :=
  brownianSignIntegral_upTo brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable a T t

end TimeTraps.Probability
