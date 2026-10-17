module

public import TimeTraps.Probability.BrownianTanakaCompensation

@[expose] public section

/-! Nondecreasing smooth time-integral corrections pass to the actual
Tanaka compensation in L². The almost-everywhere claim here is for each
fixed pair of times; no uncountable intersection is taken. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaSmoothCompensation_mono (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) {S T : ℝ≥0}
    (hST : S ≤ T) (n : ℕ) :
    ∀ᵐ ω ∂P, brownianTanakaSmoothCompensation hB hBm hjoint a S n ω ≤
      brownianTanakaSmoothCompensation hB hBm hjoint a T n ω := by
  have hi := brownianIto_drift_intervalIntegrable_ae hB
    (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a)
    (brownianTanakaSmooth_third_bound n a) hjoint T
  filter_upwards [hi, brownianTanakaSmoothCompensation_coe hB hBm hjoint a S n,
    brownianTanakaSmoothCompensation_coe hB hBm hjoint a T n] with ω hω hs ht
  rw [hs, ht]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply intervalIntegral.integral_mono_interval (le_refl 0) S.property hST _ hω
  exact Eventually.of_forall fun s =>
    tanakaSmoothShift_second_nonneg (tanakaSmoothingScale_pos n) a (B s.toNNReal ω)

theorem brownianTanakaCompensation_mono (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) {S T : ℝ≥0}
    (hST : S ≤ T) :
    ∀ᵐ ω ∂P, brownianTanakaCompensation hB hBm hjoint a S ω ≤
      brownianTanakaCompensation hB hBm hjoint a T ω := by
  let X := brownianTanakaSmoothCompensation hB hBm hjoint a S
  let Y := brownianTanakaSmoothCompensation hB hBm hjoint a T
  let U := brownianTanakaCompensation hB hBm hjoint a S
  let V := brownianTanakaCompensation hB hBm hjoint a T
  have hlim : Tendsto (fun n => Y n - X n) atTop (𝓝 (V - U)) :=
    (brownianTanakaSmoothCompensation_tendsto hB hBm hjoint a T).sub
      (brownianTanakaSmoothCompensation_tendsto hB hBm hjoint a S)
  have hn (n : ℕ) : ∀ᵐ ω ∂P, 0 ≤ (Y n - X n) ω := by
    filter_upwards [Lp.coeFn_sub (Y n) (X n),
      brownianTanakaSmoothCompensation_mono hB hBm hjoint a hST n] with ω hd hm
    rw [hd, Pi.sub_apply]
    exact sub_nonneg.mpr hm
  have h := ae_nonnegative_of_L2_tendsto _ _ hlim hn
  filter_upwards [h, Lp.coeFn_sub V U] with ω hω hd
  rw [hd, Pi.sub_apply] at hω
  exact sub_nonneg.mp hω

theorem brownianTanakaCompensation_zero (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) :
    brownianTanakaCompensation hB hBm hjoint a 0 = 0 := by
  rw [brownianTanakaCompensation, brownianSignIntegral_zero, sub_zero]
  apply Lp.ext
  filter_upwards [brownianTanakaDifferenceL2_coe B a 0 (brownianTanakaDifference_memLp hB a 0),
    Lp.coeFn_zero ℝ 2 P] with ω ha hz
  rw [ha, hz, brownianTanakaDifference_zero]
  rfl

end TimeTraps.Probability
