module

public import TimeTraps.Probability.ReflectedLocalTimeSpatialMomentCoefficient
public import TimeTraps.Probability.ReflectedInteriorLocalTimeLevelL2

@[expose] public section

/-! The coefficient difference is exactly the difference in the original
closed Brownian integral space, by equality of its product-L2 representatives. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def reflectedKinkDifferenceIntegrand (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a b : ℝ) (ha : a ∈ Ioo 0 L) (hb : b ∈ Ioo 0 L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) : brownianIntegralSpace B hBm P :=
  brownianCountableIntegrand (M := ⟨2 * σ, by positivity⟩) hB hBm hjoint
    (reflectedKinkDifference_measurable L hL a b x σ)
    (reflectedKinkDifference_bound L hL a b x hσ)
    ((reflectedInteriorKinkExceptional_countable L a x σ).union
      (reflectedInteriorKinkExceptional_countable L b x σ))
    (reflectedKinkDifference_continuousAt L hL a b ha hb x hσ) T

theorem reflectedKinkDifferenceIntegrand_coe (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a b : ℝ) (ha : a ∈ Ioo 0 L) (hb : b ∈ Ioo 0 L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (reflectedKinkDifferenceIntegrand hB hBm hjoint L hL a b ha hb x hσ T : Lp ℝ 2 ((volume : Measure ℝ).prod P))
      =ᵐ[(volume : Measure ℝ).prod P] brownianSquareProcess (fun t ω => reflectedKinkDifference L a b x σ (B t ω)) T :=
  brownianCountableIntegrand_coe hB hBm hjoint _ _ _ _ T

theorem reflectedKinkDifferenceIntegrand_eq_sub (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a b : ℝ) (ha : a ∈ Ioo 0 L) (hb : b ∈ Ioo 0 L)
    (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    reflectedKinkDifferenceIntegrand hB hBm hjoint L hL a b ha hb x hσ T =
      reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ T -
      reflectedInteriorKinkIntegrand hB hBm hjoint L hL b hb x hσ T := by
  apply Subtype.ext
  apply Lp.ext
  have hsub := Lp.coeFn_sub
    (reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ T : Lp ℝ 2 ((volume : Measure ℝ).prod P))
    (reflectedInteriorKinkIntegrand hB hBm hjoint L hL b hb x hσ T : Lp ℝ 2 ((volume : Measure ℝ).prod P))
  filter_upwards [reflectedKinkDifferenceIntegrand_coe hB hBm hjoint L hL a b ha hb x hσ T,
    reflectedInteriorKinkIntegrand_process_ae hB hBm hjoint L hL a ha x hσ T,
    reflectedInteriorKinkIntegrand_process_ae hB hBm hjoint L hL b hb x hσ T, hsub] with p hd ha' hb' hs
  change _ = ((reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ T : Lp ℝ 2 ((volume : Measure ℝ).prod P)) -
    (reflectedInteriorKinkIntegrand hB hBm hjoint L hL b hb x hσ T : Lp ℝ 2 ((volume : Measure ℝ).prod P))) p
  rw [hs, Pi.sub_apply, hd, ha', hb']
  unfold reflectedInteriorKinkProcess brownianSquareProcess reflectedKinkDifference
  ring

end TimeTraps.Probability

end
