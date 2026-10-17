module

public import TimeTraps.Probability.ReflectedLocalTimeBandWindow
public import TimeTraps.Analysis.L2FamilyMeasurableVersion

@[expose] public section

/-! A continuous family of real L2 maximal errors. A jointly measurable
representative will permit spatial averaging without an uncountable
intersection of probability-one events. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def reflectedBandErrorL2 (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (b : ℝ) : Lp ℝ 2 brownianDyadicMeasure :=
  (2 * |(reflectedBandClippedLevel a b).val - a.val|) •
      (memLp_const (1 : ℝ) : MemLp (fun _ : ℕ → ℝ => (1 : ℝ)) 2 brownianDyadicMeasure).toLp (fun _ => 1) +
    lipschitzWith_one_norm.compLp (norm_zero : ‖(0 : C(BrownianCompactTime T, ℝ))‖ = 0)
      (brownianIntegralContinuousL2 T
        (reflectedInteriorLevelIntegrand L hL x hσ T (reflectedBandClippedLevel a b) -
          reflectedInteriorLevelIntegrand L hL x hσ T a))

theorem reflectedBandErrorL2_continuous (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) :
    Continuous (reflectedBandErrorL2 L hL x hσ T a) := by
  have hc := reflectedBandClippedLevel_continuous a
  have hK : Continuous (fun b : ℝ => reflectedInteriorLevelIntegrand L hL x hσ T
      (reflectedBandClippedLevel a b) - reflectedInteriorLevelIntegrand L hL x hσ T a) :=
    ((reflectedInteriorKinkIntegrand_level_continuous brownianDyadicPath_isBrownianReal
      brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL x hσ T).comp hc).sub continuous_const
  exact (((continuous_const.mul ((continuous_subtype_val.comp hc).sub continuous_const).abs).smul
    continuous_const).add
      ((lipschitzWith_one_norm.continuous_compLp
        (norm_zero : ‖(0 : C(BrownianCompactTime T, ℝ))‖ = 0)).comp
          ((brownianIntegralContinuousL2 T).continuous.comp hK)))

theorem reflectedBandErrorL2_coe (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) (b : ℝ) :
    reflectedBandErrorL2 L hL x hσ T a b =ᵐ[brownianDyadicMeasure]
      reflectedInteriorLevelError L hL x hσ T (reflectedBandClippedLevel a b) a := by
  let one := (memLp_const (1 : ℝ) : MemLp (fun _ : ℕ → ℝ => (1 : ℝ)) 2 brownianDyadicMeasure).toLp (fun _ => 1)
  let c := 2 * |(reflectedBandClippedLevel a b).val - a.val|
  let F := brownianIntegralContinuousL2 T
    (reflectedInteriorLevelIntegrand L hL x hσ T (reflectedBandClippedLevel a b) -
      reflectedInteriorLevelIntegrand L hL x hσ T a)
  let N := lipschitzWith_one_norm.compLp (norm_zero : ‖(0 : C(BrownianCompactTime T, ℝ))‖ = 0) F
  have hn : N =ᵐ[brownianDyadicMeasure] (fun ω => ‖F ω‖) :=
    lipschitzWith_one_norm.coeFn_compLp norm_zero F
  filter_upwards [Lp.coeFn_add (c • one) N, Lp.coeFn_smul c one,
    (memLp_const (1 : ℝ) : MemLp (fun _ : ℕ → ℝ => (1 : ℝ)) 2 brownianDyadicMeasure).coeFn_toLp,
    hn] with ω hadd hsmul hone hnorm
  change (c • one + N) ω = c + ‖F ω‖
  rw [hadd, Pi.add_apply, hsmul, Pi.smul_apply, hone, smul_eq_mul, mul_one, hnorm]

theorem reflectedBandErrorL2_center (L : ℝ) (hL : 0 < L) (x : ℝ)
    {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) (a : Ioo (0 : ℝ) L) :
    reflectedBandErrorL2 L hL x hσ T a a.val = 0 := by
  simp only [reflectedBandErrorL2, reflectedBandClippedLevel_center, sub_self, abs_zero,
    mul_zero, zero_smul, map_zero, LipschitzWith.compLp_zero, add_zero]

end TimeTraps.Probability
