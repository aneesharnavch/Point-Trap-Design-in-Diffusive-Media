module

public import TimeTraps.Probability.ReflectedDiscountedPast

@[expose] public section

/-! The actual total discounted payoff splits into its past integral and
its discounted continuation. The equality follows from integrable interval
decomposition and the exact exponential factors. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedDiscounted_decomposition [IsFiniteMeasure P]
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) {α : ℝ} (hα : 0 < α)
    (f : C(Icc (0 : ℝ) L, ℝ)) (T : ℝ≥0) :
    reflectedDiscountedFuture B L hL D α x f 0 =ᵐ[P]
      (fun ω => reflectedDiscountedPast B L hL D α x f T ω +
        Real.exp (-α * T.val) * reflectedDiscountedFuture B L hL D α x f T ω) := by
  have hi := reflectedDiscounted_future_joint_integrable (P := P) B hjoint L hL D x hα f 0
  have hz : (0 : ℝ≥0).val = 0 := rfl
  simp only [hz, sub_zero] at hi
  filter_upwards [hi.prod_left_ae] with ω hω
  let g : ℝ → ℝ := fun r => Real.exp (-α * r) * reflectedContinuousInput L hL D x f (B r.toNNReal ω)
  have hg : IntegrableOn g (Ioi 0) := hω
  have he : Real.exp (-α * T.val) * reflectedDiscountedFuture B L hL D α x f T ω =
      ∫ r in Ioi T.val, g r := by
    change Real.exp (-α * T.val) * (∫ r in Ioi T.val, Real.exp (-α * (r - T.val)) *
      reflectedContinuousInput L hL D x f (B r.toNNReal ω)) = _
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with r
    dsimp only [g]
    rw [← mul_assoc, ← Real.exp_add]
    congr 2
    ring
  have hzero : reflectedDiscountedFuture B L hL D α x f 0 ω = ∫ r in Ioi (0 : ℝ), g r := by
    unfold reflectedDiscountedFuture
    simp only [hz, sub_zero, g]
  calc
    _ = ∫ r in Ioi (0 : ℝ), g r := hzero
    _ = (∫ r in (0 : ℝ)..T.val, g r) + ∫ r in Ioi T.val, g r :=
      (intervalIntegral.integral_interval_add_Ioi hg (hg.mono_set (Ioi_subset_Ioi T.coe_nonneg))).symm
    _ = _ := congrArg₂ (fun a b : ℝ => a + b) rfl he.symm

end TimeTraps.Probability
