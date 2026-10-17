module

public import TimeTraps.Probability.BrownianCountableIntegrand
public import TimeTraps.Probability.BrownianIntegralTruncation

@[expose] public section

/-! Horizon consistency of the actual bounded countable-discontinuity
integrands. Restriction is proved from their product-L² representatives,
and the conditional identity uses the original Brownian filtration. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {C : Set ℝ} {M : ℝ≥0}

theorem brownianCountableIntegrand_cutoff (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T t : ℝ≥0) :
    brownianTimeCutoff B hBm P t (brownianCountableIntegrand hB hBm hjoint hg hb hC hc T) =
      brownianCountableIntegrand hB hBm hjoint hg hb hC hc (min t T) := by
  apply Subtype.ext
  apply Lp.ext
  filter_upwards [brownianTimeCutoff_coe t (brownianCountableIntegrand hB hBm hjoint hg hb hC hc T),
    brownianCountableIntegrand_coe hB hBm hjoint hg hb hC hc T,
    brownianCountableIntegrand_coe hB hBm hjoint hg hb hC hc (min t T)] with p hcut hT hmin
  rw [hcut, hmin]
  unfold brownianBoundedProcess brownianSquareProcess at hT ⊢
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

theorem brownianCountableIntegral_upTo (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T t : ℝ≥0) :
    brownianIntegralUpTo hB.toIsPreBrownianReal t
      (brownianCountableIntegrand hB hBm hjoint hg hb hC hc T) =
      brownianCountableIntegral hB hBm hjoint hg hb hC hc (min t T) := by
  change brownianIntegral hB.toIsPreBrownianReal (brownianTimeCutoff B hBm P t
    (brownianCountableIntegrand hB hBm hjoint hg hb hC hc T)) = _
  rw [brownianCountableIntegrand_cutoff]
  rfl

theorem brownianCountableIntegral_condExp (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) (T t : ℝ≥0) :
    P[brownianCountableIntegral hB hBm hjoint hg hb hC hc T |
      brownianNaturalFiltration B hBm t] =ᵐ[P]
      brownianCountableIntegral hB hBm hjoint hg hb hC hc (min t T) := by
  have h := brownianIntegralUpTo_condExp hB.toIsPreBrownianReal t
    (brownianCountableIntegrand hB hBm hjoint hg hb hC hc T)
  rw [brownianCountableIntegral_upTo] at h
  exact h

theorem brownianCountableIntegrand_zero (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (hg : Measurable g) (hb : ∀ z, |g z| ≤ M.val)
    (hC : C.Countable) (hc : ∀ z ∉ C, ContinuousAt g z) :
    brownianCountableIntegrand hB hBm hjoint hg hb hC hc 0 = 0 := by
  apply Subtype.ext
  apply Lp.eq_zero_iff_ae_eq_zero.mpr
  filter_upwards [brownianCountableIntegrand_coe hB hBm hjoint hg hb hC hc 0] with p hp
  rw [hp]
  simp [brownianBoundedProcess, brownianSquareProcess]

end TimeTraps.Probability
