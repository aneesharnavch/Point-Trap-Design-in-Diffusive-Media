module

public import TimeTraps.Probability.BrownianIntegralFourthMixed

@[expose] public section

/-! The exact fourth-moment recursion for an actual Gaussian stochastic
update. Every mixed term is shown integrable before expansion and integration. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_fourth_update_integral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {A ξ : Ω → ℝ}
    (hA : StronglyMeasurable[brownianNaturalFiltration B hBm s] A)
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hA4 : MemLp A 4 P) (hξ4 : MemLp ξ 4 P) :
    Integrable (fun ω => (A ω + ξ ω * (B t ω - B s ω)) ^ 4) P ∧
    (∫ ω, (A ω + ξ ω * (B t ω - B s ω)) ^ 4 ∂P) =
      (∫ ω, A ω ^ 4 ∂P) + 6 * (t.val - s.val) * (∫ ω, A ω ^ 2 * ξ ω ^ 2 ∂P) +
        3 * (t.val - s.val) ^ 2 * ∫ ω, ξ ω ^ 4 ∂P := by
  let U : Ω → ℝ := fun ω => A ω ^ 3 * ξ ω * (B t ω - B s ω)
  let V : Ω → ℝ := fun ω => A ω ^ 2 * ξ ω ^ 2 * (B t ω - B s ω) ^ 2
  let W : Ω → ℝ := fun ω => A ω * ξ ω ^ 3 * (B t ω - B s ω) ^ 3
  let Q : Ω → ℝ := fun ω => (ξ ω * (B t ω - B s ω)) ^ 4
  have hmix := brownian_fourth_mixed_integrable hA4 hξ4
  have hiA := brownian_memLp_four_integrable_fourth hA4
  have hiU : Integrable U P := brownian_weighted_increment_integrable hB hBm hst
    ((hA.pow 3).mul hξ) hmix.1
  have hiV : Integrable V P := brownian_adapted_increment_power_integrable hB hBm hst
    ((hA.pow 2).mul (hξ.pow 2)) hmix.2.1 2 (brownian_increment_integrable_sq hB s t)
  have hiW : Integrable W P := brownian_adapted_increment_power_integrable hB hBm hst
    (hA.mul (hξ.pow 3)) hmix.2.2 3 (brownian_increment_integrable_cube hB s t)
  have hiQ : Integrable Q P := brownian_weighted_increment_integrable_fourth hB hBm hst hξ hξ4
  have he : (fun ω => (A ω + ξ ω * (B t ω - B s ω)) ^ 4) =
      fun ω => ((A ω ^ 4 + 4 * U ω) + 6 * V ω) + 4 * W ω + Q ω := by
    funext ω
    dsimp [U, V, W, Q]
    ring
  have hi : Integrable (fun ω => ((A ω ^ 4 + 4 * U ω) + 6 * V ω) + 4 * W ω + Q ω) P :=
    (((hiA.add (hiU.const_mul 4)).add (hiV.const_mul 6)).add (hiW.const_mul 4)).add hiQ
  constructor
  · rwa [he]
  · have hU : (∫ ω, U ω ∂P) = 0 :=
      brownian_weighted_increment_mean hB hBm hst ((hA.pow 3).mul hξ) hmix.1
    have hV : (∫ ω, V ω ∂P) = (t.val - s.val) * ∫ ω, A ω ^ 2 * ξ ω ^ 2 ∂P := by
      have hv := brownian_adapted_increment_power_mean hB hBm hst ((hA.pow 2).mul (hξ.pow 2)) 2
      rw [brownian_increment_second_moment hB s t,
        abs_of_nonneg (sub_nonneg.mpr (show s.val ≤ t.val from hst))] at hv
      exact hv.trans (mul_comm _ _)
    have hW : (∫ ω, W ω ∂P) = 0 := by
      have hw := brownian_adapted_increment_power_mean hB hBm hst (hA.mul (hξ.pow 3)) 3
      rw [brownian_increment_cube_moment hB s t, mul_zero] at hw
      exact hw
    have hQ : (∫ ω, Q ω ∂P) = 3 * (t.val - s.val) ^ 2 * ∫ ω, ξ ω ^ 4 ∂P :=
      brownian_weighted_increment_fourth_moment hB hBm hst hξ hξ4
    have h₁ : Integrable (fun ω => A ω ^ 4 + 4 * U ω) P := hiA.add (hiU.const_mul 4)
    have h₂ : Integrable (fun ω => (A ω ^ 4 + 4 * U ω) + 6 * V ω) P := h₁.add (hiV.const_mul 6)
    have h₃ : Integrable (fun ω => ((A ω ^ 4 + 4 * U ω) + 6 * V ω) + 4 * W ω) P := h₂.add (hiW.const_mul 4)
    rw [he, integral_add h₃ hiQ, integral_add h₂ (hiW.const_mul 4),
      integral_add h₁ (hiV.const_mul 6), integral_add hiA (hiU.const_mul 4)]
    simp only [integral_const_mul, hU, hV, hW, hQ]
    ring

theorem brownian_fourth_update_memLp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {s t : ℝ≥0} (hst : s ≤ t) {A ξ : Ω → ℝ}
    (hA : StronglyMeasurable[brownianNaturalFiltration B hBm s] A)
    (hξ : StronglyMeasurable[brownianNaturalFiltration B hBm s] ξ)
    (hA4 : MemLp A 4 P) (hξ4 : MemLp ξ 4 P) :
    MemLp (fun ω => A ω + ξ ω * (B t ω - B s ω)) 4 P :=
  brownian_fourth_memLp_of_integrable
    (hA4.aestronglyMeasurable.add (hξ4.aestronglyMeasurable.mul (((hBm t).sub (hBm s)).aestronglyMeasurable)))
    (brownian_fourth_update_integral hB hBm hst hA hξ hA4 hξ4).1

end TimeTraps.Probability
