module

public import TimeTraps.Analysis.IntervalPointRegularityLocal
public import TimeTraps.Analysis.PiecewiseDistributionCalculus

@[expose] public section

/-! Green identities for the derived AC/L2 slope, retaining both boundary
traces and allowing arbitrary signed H1 tests. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter

theorem interval_regular_pairing_congr {a b ψ : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hab : a =ᵐ[volume.restrict (Ioo l r)] b) :
    (∫ x in l..r, a x * ψ x) = ∫ x in l..r, b x * ψ x := by
  simp only [intervalIntegral.integral_of_le hlr, integral_Ioc_eq_integral_Ioo]
  apply integral_congr_ae
  filter_upwards [hab] with x hx
  rw [hx]

theorem IntervalSlopeRegularity.green_identity {u v g ψ : ℝ → ℝ} {l r : ℝ}
    (h : IntervalSlopeRegularity u v g l r) (hlr : l ≤ r) (hψ : IntervalEnergy ψ l r) :
    (∫ x in l..r, deriv u x * deriv ψ x) =
      v r * ψ r - v l * ψ l - ∫ x in l..r, g x * ψ x := by
  rw [interval_regular_pairing_congr hlr h.slope_ae,
    h.slope_energy.absolutelyContinuous.integral_mul_deriv_eq_deriv_mul hψ.absolutelyContinuous,
    interval_regular_pairing_congr hlr h.second_ae]

theorem IntervalSlopeRegularity.poisson_green_identity {u v f ψ : ℝ → ℝ} {D l r : ℝ}
    (h : IntervalSlopeRegularity u v (fun x => -f x / D) l r)
    (hD : D ≠ 0) (hlr : l ≤ r) (hψ : IntervalEnergy ψ l r) :
    D * (∫ x in l..r, deriv u x * deriv ψ x) =
      (∫ x in l..r, f x * ψ x) + D * v r * ψ r - D * v l * ψ l := by
  have hi : (∫ x in l..r, (-f x / D) * ψ x) = -(∫ x in l..r, f x * ψ x) / D := by
    calc
      _ = ∫ x in l..r, -(f x * ψ x) / D := by
        apply intervalIntegral.integral_congr
        intro x _
        ring
      _ = _ := by rw [intervalIntegral.integral_div, intervalIntegral.integral_neg]
  rw [h.green_identity hlr hψ, hi]
  field_simp
  ring

end TimeTraps.Analysis
