module

public import TimeTraps.Probability.BrownianIntegralCovariance

@[expose] public section

/-! The covariance of two elementary adapted integrals is the length of the
overlap of their time intervals times the coefficient pairing. This gives
a common-representation identity without selecting a sorted refinement. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def brownianIntervalOverlap (s t u v : ℝ≥0) : ℝ :=
  max ((min t v).val - (max s u).val) 0

theorem brownianIntervalOverlap_symm (s t u v : ℝ≥0) :
    brownianIntervalOverlap s t u v = brownianIntervalOverlap u v s t := by
  simp only [brownianIntervalOverlap, min_comm t v, max_comm s u]

theorem brownian_weighted_increment_covariance_ordered (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t u v : ℝ≥0}
    (hst : s ≤ t) (huv : u ≤ v) (hsu : s ≤ u) {ξ η : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hη : StronglyMeasurable[brownianNaturalFiltration B hBm u] η)
    (hξ2 : MemLp ξ 2 P) (hη2 : MemLp η 2 P) :
    (∫ ω, (ξ ω * (B t ω - B s ω)) * (η ω * (B v ω - B u ω)) ∂P) =
      brownianIntervalOverlap s t u v * ∫ ω, ξ ω * η ω ∂P := by
  by_cases htu : t ≤ u
  · have hlen : (min t v).val - u.val ≤ 0 :=
      sub_nonpos.mpr (show (min t v).val ≤ u.val from (min_le_left t v).trans htu)
    rw [brownian_weighted_increment_disjoint hB hBm hst htu huv hξ hη hξ2 hη2]
    simp only [brownianIntervalOverlap, max_eq_right hsu, max_eq_right hlen, zero_mul]
  · have hut : u ≤ t := le_of_not_ge htu
    have hξu := hξ.mono ((brownianNaturalFiltration B hBm).mono hsu)
    have hX := brownian_weighted_increment_memLp hB hBm hsu hξ hξ2
    have hZ := brownian_weighted_increment_memLp hB hBm hut hξu hξ2
    have hY := brownian_weighted_increment_memLp hB hBm huv hη hη2
    have hlen : 0 ≤ (min t v).val - u.val :=
      sub_nonneg.mpr (show u.val ≤ (min t v).val from le_min hut huv)
    calc
      _ = ∫ ω, (ξ ω * (B u ω - B s ω)) * (η ω * (B v ω - B u ω)) +
          (ξ ω * (B t ω - B u ω)) * (η ω * (B v ω - B u ω)) ∂P := by
        apply integral_congr_ae
        filter_upwards [] with ω
        ring
      _ = (∫ ω, (ξ ω * (B u ω - B s ω)) * (η ω * (B v ω - B u ω)) ∂P) +
          ∫ ω, (ξ ω * (B t ω - B u ω)) * (η ω * (B v ω - B u ω)) ∂P :=
        integral_add (hX.integrable_mul hY) (hZ.integrable_mul hY)
      _ = _ := by
        rw [brownian_weighted_increment_disjoint hB hBm hsu le_rfl huv hξ hη hξ2 hη2,
          brownian_weighted_increment_same_left hB hBm hut huv hξu hη hξ2 hη2, zero_add]
        simp only [brownianIntervalOverlap, max_eq_right hsu, max_eq_left hlen]

theorem brownian_weighted_increment_covariance (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t u v : ℝ≥0}
    (hst : s ≤ t) (huv : u ≤ v) {ξ η : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hη : StronglyMeasurable[brownianNaturalFiltration B hBm u] η)
    (hξ2 : MemLp ξ 2 P) (hη2 : MemLp η 2 P) :
    (∫ ω, (ξ ω * (B t ω - B s ω)) * (η ω * (B v ω - B u ω)) ∂P) =
      brownianIntervalOverlap s t u v * ∫ ω, ξ ω * η ω ∂P := by
  rcases le_total s u with hsu | hus
  · exact brownian_weighted_increment_covariance_ordered hB hBm hst huv hsu hξ hη hξ2 hη2
  · have h := brownian_weighted_increment_covariance_ordered hB hBm huv hst hus hη hξ hη2 hξ2
    rw [brownianIntervalOverlap_symm u v s t] at h
    simpa only [mul_comm] using h

end TimeTraps.Probability
