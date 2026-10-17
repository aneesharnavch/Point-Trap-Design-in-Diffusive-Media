module

public import TimeTraps.Probability.ReflectedInteriorKinkIntegrandData

@[expose] public section

/-! The interior-kink stochastic coefficient belongs to the actual
original-Brownian closed integrand space. The physical diffusion scale
appears once, outside the normalized bounded coefficient; all finite
horizons are genuine product-L² restrictions. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def reflectedInteriorKinkIntegrand (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) : brownianIntegralSpace B hBm P :=
  σ • brownianCountableIntegrand (M := 1) hB hBm hjoint
    (reflectedInteriorKinkCoefficient_measurable L hL a x σ)
    (reflectedInteriorKinkCoefficient_bound L hL a x σ)
    (reflectedInteriorKinkExceptional_countable L a x σ)
    (reflectedInteriorKinkCoefficient_continuousAt L hL a ha x hσ) T

theorem reflectedInteriorKinkIntegrand_coe (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    (reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ T :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      brownianSquareProcess (fun t ω => σ * Real.sign (reflectedFold L (x + σ * B t ω) - a) *
        reflectedFoldSlope L (x + σ * B t ω)) T := by
  let A := brownianCountableIntegrand (M := 1) hB hBm hjoint
    (reflectedInteriorKinkCoefficient_measurable L hL a x σ)
    (reflectedInteriorKinkCoefficient_bound L hL a x σ)
    (reflectedInteriorKinkExceptional_countable L a x σ)
    (reflectedInteriorKinkCoefficient_continuousAt L hL a ha x hσ) T
  have hA := brownianCountableIntegrand_coe (M := 1) hB hBm hjoint
    (reflectedInteriorKinkCoefficient_measurable L hL a x σ)
    (reflectedInteriorKinkCoefficient_bound L hL a x σ)
    (reflectedInteriorKinkExceptional_countable L a x σ)
    (reflectedInteriorKinkCoefficient_continuousAt L hL a ha x hσ) T
  change (A : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
    brownianBoundedProcess B (reflectedInteriorKinkCoefficient L a x σ) T at hA
  change (σ • (A : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] _
  filter_upwards [Lp.coeFn_smul σ (A : Lp ℝ 2 ((volume : Measure ℝ).prod P)), hA] with p hs hp
  rw [hs]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hp]
  unfold brownianBoundedProcess brownianSquareProcess reflectedInteriorKinkCoefficient
    reflectedInteriorTanakaSlope
  ring

theorem reflectedInteriorKinkIntegrand_cutoff (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T t : ℝ≥0) :
    brownianTimeCutoff B hBm P t (reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ T) =
      reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ (min t T) := by
  unfold reflectedInteriorKinkIntegrand
  rw [map_smul]
  exact congrArg (fun u : brownianIntegralSpace B hBm P => σ • u)
    (brownianCountableIntegrand_cutoff (M := 1) hB hBm hjoint
      (reflectedInteriorKinkCoefficient_measurable L hL a x σ)
      (reflectedInteriorKinkCoefficient_bound L hL a x σ)
      (reflectedInteriorKinkExceptional_countable L a x σ)
      (reflectedInteriorKinkCoefficient_continuousAt L hL a ha x hσ) T t)

def reflectedInteriorKinkIntegral (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) : Lp ℝ 2 P :=
  brownianIntegral hB.toIsPreBrownianReal (reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ T)

theorem reflectedInteriorKinkIntegral_upTo (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T t : ℝ≥0) :
    brownianIntegralUpTo hB.toIsPreBrownianReal t
      (reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ T) =
      reflectedInteriorKinkIntegral hB hBm hjoint L hL a ha x hσ (min t T) := by
  change brownianIntegral hB.toIsPreBrownianReal (brownianTimeCutoff B hBm P t
    (reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ T)) = _
  rw [reflectedInteriorKinkIntegrand_cutoff]
  rfl

theorem reflectedInteriorKinkIntegrand_zero (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) :
    reflectedInteriorKinkIntegrand hB hBm hjoint L hL a ha x hσ 0 = 0 := by
  unfold reflectedInteriorKinkIntegrand
  have he := brownianCountableIntegrand_zero (M := 1) hB hBm hjoint
    (reflectedInteriorKinkCoefficient_measurable L hL a x σ)
    (reflectedInteriorKinkCoefficient_bound L hL a x σ)
    (reflectedInteriorKinkExceptional_countable L a x σ)
    (reflectedInteriorKinkCoefficient_continuousAt L hL a ha x hσ)
  exact (congrArg (fun u : brownianIntegralSpace B hBm P => σ • u) he).trans (smul_zero σ)

end TimeTraps.Probability

end
