module

public import TimeTraps.Analysis.IntervalEnergyTrace

@[expose] public section

/-! Adjustable point-trace estimates for every signed physical H1 function.
A closed subinterval of prescribed length containing the evaluation point
gives an arbitrarily small derivative-energy coefficient. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem IntervalEnergy.trace_sq_le_of_scale {u : ℝ → ℝ} {l r x δ : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l < r) (hx : x ∈ Icc l r)
    (hδ : 0 < δ) (hδL : δ ≤ r - l) :
    u x ^ 2 ≤ (2 / δ) * (∫ t in l..r, u t ^ 2) +
      2 * δ * (∫ t in l..r, deriv u t ^ 2) := by
  let a := min x (r - δ)
  let b := a + δ
  have hla : l ≤ a := le_min hx.1 (by linarith)
  have hab : a < b := by dsimp [b]; linarith
  have hbr : b ≤ r := by
    have ha := min_le_right x (r - δ)
    dsimp only [b, a]
    linarith
  have hax : a ≤ x := min_le_left _ _
  have hxb : x ≤ b := by
    rcases le_total x (r - δ) with h | h
    · simp only [b, a, min_eq_left h]
      linarith
    · simp only [b, a, min_eq_right h]
      linarith [hx.2]
  have hv : IntervalEnergy u a b := hu.mono (by
    rw [uIcc_of_le hab.le, uIcc_of_le hlr.le]
    exact Icc_subset_Icc hla hbr)
  have hm : (∫ t in a..b, u t ^ 2) ≤ ∫ t in l..r, u t ^ 2 :=
    intervalIntegral.integral_mono_interval hla hab.le hbr
      (Filter.Eventually.of_forall fun t => sq_nonneg (u t)) hu.state_square_integrable
  have hE : (∫ t in a..b, deriv u t ^ 2) ≤ ∫ t in l..r, deriv u t ^ 2 :=
    intervalIntegral.integral_mono_interval hla hab.le hbr
      (Filter.Eventually.of_forall fun t => sq_nonneg (deriv u t))
      hu.derivative_square_integrable
  have ht := hv.trace_sq_le hab ⟨hax, hxb⟩
  have hlen : b - a = δ := by dsimp only [b]; ring
  rw [hlen] at ht
  exact ht.trans (add_le_add
    (mul_le_mul_of_nonneg_left hm (div_nonneg (by norm_num) hδ.le))
    (mul_le_mul_of_nonneg_left hE (by positivity)))

/-- The derivative coefficient can be made arbitrarily small; the mass
coefficient is explicit and finite for every positive epsilon. -/
theorem IntervalEnergy.trace_sq_interpolation {u : ℝ → ℝ} {l r x ε : ℝ}
    (hu : IntervalEnergy u l r) (hlr : l < r) (hx : x ∈ Icc l r) (hε : 0 < ε) :
    u x ^ 2 ≤ (2 / (r - l) + 2 / ε) * (∫ t in l..r, u t ^ 2) +
      2 * ε * (∫ t in l..r, deriv u t ^ 2) := by
  have hm : 0 ≤ ∫ t in l..r, u t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hlr.le (fun t => sq_nonneg (u t))
  have hE : 0 ≤ ∫ t in l..r, deriv u t ^ 2 :=
    intervalIntegral.integral_nonneg_of_forall hlr.le (fun t => sq_nonneg (deriv u t))
  rcases le_total ε (r - l) with h | h
  · have ht := hu.trace_sq_le_of_scale hlr hx hε h
    have hp := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (sub_pos.mpr hlr).le) hm
    nlinarith
  · have ht := hu.trace_sq_le hlr hx
    have hp := mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 2) hε.le) hm
    have hd := mul_le_mul_of_nonneg_right h hE
    nlinarith

end TimeTraps.Analysis
