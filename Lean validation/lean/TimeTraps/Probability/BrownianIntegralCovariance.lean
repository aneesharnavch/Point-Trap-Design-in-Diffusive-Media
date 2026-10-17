module

public import TimeTraps.Probability.BrownianStepIntegralIsometry

@[expose] public section

/-! Covariances of elementary adapted stochastic integrals. These identities
will identify different representations of the same time-dependent process
in the product-measure L² space. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_weighted_increment_same_interval (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {ξ η : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hη : StronglyMeasurable[brownianNaturalFiltration B hBm s] η)
    (hξ2 : MemLp ξ 2 P) (hη2 : MemLp η 2 P) :
    (∫ ω, (ξ ω * (B t ω - B s ω)) * (η ω * (B t ω - B s ω)) ∂P) =
      (t.val - s.val) * ∫ ω, ξ ω * η ω ∂P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hi := (brownian_weighted_increment_memLp hB hBm hst hξ hξ2).integrable_mul
    (brownian_weighted_increment_memLp hB hBm hst hη hη2)
  have he : (fun ω => (ξ ω * (B t ω - B s ω)) * (η ω * (B t ω - B s ω))) =
      (ξ * η) * (fun ω => (B t ω - B s ω) ^ 2) := by
    funext ω
    simp only [Pi.mul_apply]
    ring
  have hip : Integrable ((ξ * η) * (fun ω => (B t ω - B s ω) ^ 2)) P := by
    rw [← he]
    exact hi
  have hc := condExp_mul_of_stronglyMeasurable_left (hξ.mul hη) hip
    (brownian_increment_integrable_sq hB s t)
  have hc' : P[(ξ * η) * (fun ω => (B t ω - B s ω) ^ 2) |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => (ξ ω * η ω) * (t.val - s.val) := by
    refine hc.trans ?_
    filter_upwards [brownian_increment_square_condExp hB hBm hst] with ω hω
    change (ξ ω * η ω) * P[fun ω => (B t ω - B s ω) ^ 2 |
      brownianNaturalFiltration B hBm s] ω = _
    rw [hω]
  calc
    _ = ∫ ω, ((ξ * η) * (fun ω => (B t ω - B s ω) ^ 2)) ω ∂P := by rw [← he]
    _ = ∫ ω, P[(ξ * η) * (fun ω => (B t ω - B s ω) ^ 2) |
        brownianNaturalFiltration B hBm s] ω ∂P :=
      (integral_condExp ((brownianNaturalFiltration B hBm).le s)).symm
    _ = ∫ ω, (ξ ω * η ω) * (t.val - s.val) ∂P := integral_congr_ae hc'
    _ = _ := by rw [integral_mul_const, mul_comm]

theorem brownian_weighted_increment_disjoint (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t u v : ℝ≥0}
    (hst : s ≤ t) (htu : t ≤ u) (huv : u ≤ v) {ξ η : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hη : StronglyMeasurable[brownianNaturalFiltration B hBm u] η)
    (hξ2 : MemLp ξ 2 P) (hη2 : MemLp η 2 P) :
    (∫ ω, (ξ ω * (B t ω - B s ω)) * (η ω * (B v ω - B u ω)) ∂P) = 0 := by
  have hl := (brownianNaturalFiltration B hBm).mono (hst.trans htu)
  have hr := (brownianNaturalFiltration B hBm).mono htu
  have hZ : StronglyMeasurable[brownianNaturalFiltration B hBm u]
      (fun ω => ξ ω * (B t ω - B s ω)) :=
    (hξ.mono hl).mul
      (((brownianNaturalFiltration_stronglyAdapted B hBm t).mono hr).sub
        ((brownianNaturalFiltration_stronglyAdapted B hBm s).mono hl))
  exact brownian_weighted_increment_orthogonal hB hBm huv hZ hη
    (brownian_weighted_increment_memLp hB hBm hst hξ hξ2) hη2

theorem brownian_weighted_increment_same_left_ordered (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t v : ℝ≥0} (hst : s ≤ t) (htv : t ≤ v)
    {ξ η : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hη : StronglyMeasurable[brownianNaturalFiltration B hBm s] η)
    (hξ2 : MemLp ξ 2 P) (hη2 : MemLp η 2 P) :
    (∫ ω, (ξ ω * (B t ω - B s ω)) * (η ω * (B v ω - B s ω)) ∂P) =
      (t.val - s.val) * ∫ ω, ξ ω * η ω ∂P := by
  have hηt := hη.mono ((brownianNaturalFiltration B hBm).mono hst)
  have hX := brownian_weighted_increment_memLp hB hBm hst hξ hξ2
  have hY := brownian_weighted_increment_memLp hB hBm hst hη hη2
  have hZ := brownian_weighted_increment_memLp hB hBm htv hηt hη2
  calc
    _ = ∫ ω, (ξ ω * (B t ω - B s ω)) * (η ω * (B t ω - B s ω)) +
        (ξ ω * (B t ω - B s ω)) * (η ω * (B v ω - B t ω)) ∂P := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = (∫ ω, (ξ ω * (B t ω - B s ω)) * (η ω * (B t ω - B s ω)) ∂P) +
        ∫ ω, (ξ ω * (B t ω - B s ω)) * (η ω * (B v ω - B t ω)) ∂P :=
      integral_add (hX.integrable_mul hY) (hX.integrable_mul hZ)
    _ = _ := by
      rw [brownian_weighted_increment_same_interval hB hBm hst hξ hη hξ2 hη2,
        brownian_weighted_increment_disjoint hB hBm hst le_rfl htv hξ hηt hξ2 hη2,
        add_zero]

theorem brownian_weighted_increment_same_left (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t v : ℝ≥0} (hst : s ≤ t) (hsv : s ≤ v)
    {ξ η : Ω → ℝ}
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hη : StronglyMeasurable[brownianNaturalFiltration B hBm s] η)
    (hξ2 : MemLp ξ 2 P) (hη2 : MemLp η 2 P) :
    (∫ ω, (ξ ω * (B t ω - B s ω)) * (η ω * (B v ω - B s ω)) ∂P) =
      ((min t v).val - s.val) * ∫ ω, ξ ω * η ω ∂P := by
  rcases le_total t v with htv | hvt
  · simpa only [min_eq_left htv] using
      brownian_weighted_increment_same_left_ordered hB hBm hst htv hξ hη hξ2 hη2
  · have h := brownian_weighted_increment_same_left_ordered hB hBm hsv hvt hη hξ hη2 hξ2
    simpa only [min_eq_right hvt, mul_comm] using h

end TimeTraps.Probability
