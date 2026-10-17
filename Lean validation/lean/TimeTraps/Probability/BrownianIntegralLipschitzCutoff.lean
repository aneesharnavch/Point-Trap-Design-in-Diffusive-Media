module

public import TimeTraps.Probability.BrownianIntegralLipschitz
public import TimeTraps.Probability.BrownianIntegralTruncation

@[expose] public section

/-! Exact time cutoff of the actual integral of a Lipschitz function of
Brownian motion. The finite-horizon integrals have compatible conditional
expectations in the original raw Brownian filtration. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {K : ℝ≥0}

theorem brownianLipschitzIntegrand_cutoff (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T t : ℝ≥0) :
    brownianTimeCutoff B hBm P t (brownianLipschitzIntegrand hB hBm hg hjoint T) =
      brownianLipschitzIntegrand hB hBm hg hjoint (min t T) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [brownianTimeCutoff_coe t (brownianLipschitzIntegrand hB hBm hg hjoint T),
    brownianLipschitzIntegrand_coe hB hBm hg hjoint T,
    brownianLipschitzIntegrand_coe hB hBm hg hjoint (min t T)] with p hcut hT hmin
  rw [hcut, hmin]
  by_cases ht : p.1 ≤ t.val
  · have hp : p ∈ brownianTimePast t := ht
    rw [indicator_of_mem hp, hT]
    have hle : p.1 ≤ (min t T).val ↔ p.1 ≤ T.val := by
      change p.1 ≤ min t.val T.val ↔ p.1 ≤ T.val
      simp only [le_min_iff, ht, true_and]
    simp only [brownianLipschitzProcess, brownianSquareProcess, indicator_apply, mem_Ioc, hle]
  · have hp : p ∉ brownianTimePast t := ht
    rw [indicator_of_notMem hp]
    have hn : p.1 ∉ Ioc (0 : ℝ) (min t T).val := by
      intro h
      exact ht (h.2.trans (min_le_left t.val T.val))
    simp only [brownianLipschitzProcess, brownianSquareProcess, indicator_of_notMem hn, zero_mul]

theorem brownianLipschitzIntegral_upTo (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T t : ℝ≥0) :
    brownianIntegralUpTo hB t (brownianLipschitzIntegrand hB hBm hg hjoint T) =
      brownianIntegral hB (brownianLipschitzIntegrand hB hBm hg hjoint (min t T)) := by
  change brownianIntegral hB (brownianTimeCutoff B hBm P t
    (brownianLipschitzIntegrand hB hBm hg hjoint T)) = _
  rw [brownianLipschitzIntegrand_cutoff]

theorem brownianLipschitzIntegral_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T t : ℝ≥0) :
    P[brownianIntegral hB (brownianLipschitzIntegrand hB hBm hg hjoint T) |
      brownianNaturalFiltration B hBm t] =ᵐ[P]
      brownianIntegral hB (brownianLipschitzIntegrand hB hBm hg hjoint (min t T)) := by
  have h := brownianIntegralUpTo_condExp hB t (brownianLipschitzIntegrand hB hBm hg hjoint T)
  rw [brownianLipschitzIntegral_upTo] at h
  exact h

end TimeTraps.Probability
