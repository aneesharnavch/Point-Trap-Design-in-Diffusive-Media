module

public import TimeTraps.Probability.ReflectedC2ItoIntegrandData
public import TimeTraps.Probability.BrownianAdaptedContinuousMultiplier
public import TimeTraps.Probability.BrownianFoldSlopeCutoff

@[expose] public section

/-! The original-Brownian Itô integrand for a general globally C² test
of the folded trajectory. Multiplication by the derived bounded derivative
process preserves the actual closed integrand domain. The diffusion scale
is sqrt(2D), and finite horizons are actual product-L² cutoffs. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

def reflectedC2ItoMultiplier {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) :
    brownianIntegralSpace B hBm P →L[ℝ] brownianIntegralSpace B hBm P :=
  brownianAdaptedContinuousMultiplier hB.toIsPreBrownianReal hBm
    (reflectedC2DerivativeProcess_stronglyAdapted hF hBm L D x)
    (reflectedC2DerivativeProcess_jointlyMeasurable hF hjoint L D x)
    (reflectedC2DerivativeProcess_bound hF B L hL D x)
    (reflectedC2DerivativeProcess_continuous_ae hF hB L D x)

def reflectedC2ItoIntegrand {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    brownianIntegralSpace B hBm P :=
  Real.sqrt (2 * D) • reflectedC2ItoMultiplier hF hB hBm hjoint L hL D x
    (brownianFoldSlopeIntegrand hB.toIsPreBrownianReal hBm hjoint L hL x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T)

theorem reflectedC2ItoIntegrand_coe {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (reflectedC2ItoIntegrand hF hB hBm hjoint L hL D hD x T :
      Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
      brownianSquareProcess (fun t ω => Real.sqrt (2 * D) * deriv F (foldedTrajectory L D x B t ω) *
        reflectedFoldSlope L (x + Real.sqrt (2 * D) * B t ω)) T := by
  let A := brownianFoldSlopeIntegrand hB.toIsPreBrownianReal hBm hjoint L hL x
    (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T
  let M := reflectedC2ItoMultiplier hF hB hBm hjoint L hL D x
  have hm := brownianAdaptedContinuousMultiplier_coe hB.toIsPreBrownianReal hBm
    (reflectedC2DerivativeProcess_stronglyAdapted hF hBm L D x)
    (reflectedC2DerivativeProcess_jointlyMeasurable hF hjoint L D x)
    (reflectedC2DerivativeProcess_bound hF B L hL D x)
    (reflectedC2DerivativeProcess_continuous_ae hF hB L D x) A
  change (M A : Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P]
    (fun p => reflectedC2DerivativeProcess F B L D x p.1.toNNReal p.2 *
      (A : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p) at hm
  change (Real.sqrt (2 * D) • (M A : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P)) =ᵐ[volume.prod P] _
  filter_upwards [Lp.coeFn_smul (Real.sqrt (2 * D)) (M A : Lp ℝ 2 ((volume : Measure ℝ).prod P)),
    hm, brownianFoldSlopeIntegrand_coe hB.toIsPreBrownianReal hBm hjoint L hL x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T] with p hc hm hp
  change (A : Lp ℝ 2 ((volume : Measure ℝ).prod P)) p =
    brownianBoundedProcess B (fun z => reflectedFoldSlope L (x + Real.sqrt (2 * D) * z)) T p at hp
  rw [hc]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hm, hp]
  unfold reflectedC2DerivativeProcess brownianBoundedProcess brownianSquareProcess
  ring

theorem reflectedC2ItoIntegrand_cutoff {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T t : ℝ≥0) :
    brownianTimeCutoff B hBm P t (reflectedC2ItoIntegrand hF hB hBm hjoint L hL D hD x T) =
      reflectedC2ItoIntegrand hF hB hBm hjoint L hL D hD x (min t T) := by
  unfold reflectedC2ItoIntegrand reflectedC2ItoMultiplier
  rw [map_smul, ← brownianAdaptedContinuousMultiplier_cutoff, brownianFoldSlopeIntegrand_cutoff]

def reflectedC2ItoIntegral {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) : Lp ℝ 2 P :=
  brownianIntegral hB.toIsPreBrownianReal (reflectedC2ItoIntegrand hF hB hBm hjoint L hL D hD x T)

theorem reflectedC2ItoIntegral_upTo {F : ℝ → ℝ} (hF : ContDiff ℝ 2 F)
    (hB : IsBrownianReal B P) (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T t : ℝ≥0) :
    brownianIntegralUpTo hB.toIsPreBrownianReal t (reflectedC2ItoIntegrand hF hB hBm hjoint L hL D hD x T) =
      reflectedC2ItoIntegral hF hB hBm hjoint L hL D hD x (min t T) := by
  change brownianIntegral hB.toIsPreBrownianReal (brownianTimeCutoff B hBm P t
    (reflectedC2ItoIntegrand hF hB hBm hjoint L hL D hD x T)) = _
  rw [reflectedC2ItoIntegrand_cutoff]
  rfl

end TimeTraps.Probability

end
