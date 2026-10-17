module

public import TimeTraps.Probability.BrownianIntegralOverlap
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

@[expose] public section

/-! Elementary time-dependent processes in the actual product-measure L²
space. Their pairings are overlap lengths times coefficient pairings. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}

noncomputable def brownianIntervalIndicator (s t : ℝ≥0) : ℝ → ℝ :=
  (Ioc s.val t.val).indicator (fun _ => 1)

theorem brownianIntervalIndicator_measurable (s t : ℝ≥0) :
    Measurable (brownianIntervalIndicator s t) :=
  measurable_const.indicator measurableSet_Ioc

theorem brownianIntervalIndicator_integrable (s t : ℝ≥0) :
    Integrable (brownianIntervalIndicator s t) volume :=
  (integrableOn_const (μ := volume) (s := Ioc s.val t.val)
    (C := (1 : ℝ)) (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)).integrable_indicator
      measurableSet_Ioc

theorem brownianIntervalIndicator_integral (s t : ℝ≥0) :
    (∫ r, brownianIntervalIndicator s t r) = max (t.val - s.val) 0 := by
  rw [brownianIntervalIndicator, integral_indicator measurableSet_Ioc, setIntegral_const]
  simp only [smul_eq_mul, mul_one, Real.volume_real_Ioc]

theorem brownianIntervalIndicator_mul (s t u v : ℝ≥0) (r : ℝ) :
    brownianIntervalIndicator s t r * brownianIntervalIndicator u v r =
      brownianIntervalIndicator (max s u) (min t v) r := by
  have hm : r ∈ Ioc (max s u).val (min t v).val ↔
      r ∈ Ioc s.val t.val ∧ r ∈ Ioc u.val v.val := by
    change (max s.val u.val < r ∧ r ≤ min t.val v.val) ↔
      (s.val < r ∧ r ≤ t.val) ∧ (u.val < r ∧ r ≤ v.val)
    simp only [max_lt_iff, le_min_iff]
    tauto
  by_cases hs : r ∈ Ioc s.val t.val <;> by_cases hu : r ∈ Ioc u.val v.val <;>
    simp only [brownianIntervalIndicator, Set.indicator_apply, hm, hs, hu,
      and_self, and_false, false_and, ite_true, ite_false, mul_one, mul_zero]

noncomputable def brownianElementaryProcess (s t : ℝ≥0) (ξ : Ω → ℝ) (p : ℝ × Ω) : ℝ :=
  brownianIntervalIndicator s t p.1 * ξ p.2

theorem brownianElementaryProcess_measurable (s t : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : Measurable ξ) : Measurable (brownianElementaryProcess s t ξ) :=
  ((brownianIntervalIndicator_measurable s t).comp measurable_fst).mul
    (hξ.comp measurable_snd)

theorem brownianElementaryProcess_memLp (s t : ℝ≥0) {ξ : Ω → ℝ}
    (hξ : Measurable ξ) (hξ2 : MemLp ξ 2 P) :
    MemLp (brownianElementaryProcess s t ξ) 2 (volume.prod P) := by
  apply (memLp_two_iff_integrable_sq
    (brownianElementaryProcess_measurable s t hξ).aestronglyMeasurable).mpr
  have h := (brownianIntervalIndicator_integrable s t).mul_prod hξ2.integrable_sq
  convert! h using 1
  funext p
  change (brownianIntervalIndicator s t p.1 * ξ p.2) ^ 2 =
    brownianIntervalIndicator s t p.1 * ξ p.2 ^ 2
  rw [mul_pow, pow_two (brownianIntervalIndicator s t p.1),
    brownianIntervalIndicator_mul, max_self, min_self]

theorem brownianElementaryProcess_pairing [SFinite P] (s t u v : ℝ≥0) (ξ η : Ω → ℝ) :
    (∫ p, brownianElementaryProcess s t ξ p * brownianElementaryProcess u v η p
      ∂volume.prod P) = brownianIntervalOverlap s t u v * ∫ ω, ξ ω * η ω ∂P := by
  calc
    _ = ∫ p : ℝ × Ω, brownianIntervalIndicator (max s u) (min t v) p.1 *
        (ξ p.2 * η p.2) ∂volume.prod P := by
      apply integral_congr_ae
      filter_upwards [] with p
      dsimp only [brownianElementaryProcess]
      rw [show brownianIntervalIndicator s t p.1 * ξ p.2 *
          (brownianIntervalIndicator u v p.1 * η p.2) =
          (brownianIntervalIndicator s t p.1 * brownianIntervalIndicator u v p.1) *
            (ξ p.2 * η p.2) by ring, brownianIntervalIndicator_mul]
    _ = (∫ r, brownianIntervalIndicator (max s u) (min t v) r) *
        ∫ ω, ξ ω * η ω ∂P :=
      integral_prod_mul (μ := volume) (ν := P) (L := ℝ)
        (brownianIntervalIndicator (max s u) (min t v)) (fun ω => ξ ω * η ω)
    _ = _ := by rw [brownianIntervalIndicator_integral]; rfl

end TimeTraps.Probability
