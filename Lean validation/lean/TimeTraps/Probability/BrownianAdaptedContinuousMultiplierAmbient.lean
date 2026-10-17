module

public import TimeTraps.Probability.BrownianAdaptedContinuousIntegrand

@[expose] public section

/-! Bounded measurable multiplication on the actual ambient product L²
space. The operator is constructed from pointwise multiplication of
representatives, with equality understood almost everywhere. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {K : ℝ × Ω → ℝ} {M : ℝ≥0}

theorem brownianAdaptedContinuousMultiplier_memLp (hK : Measurable K)
    (hb : ∀ p, |K p| ≤ M.val) (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    MemLp (fun p => K p * f p) 2 (volume.prod P) := by
  apply (Lp.memLp f).of_le_mul (c := M.val)
    (hK.aestronglyMeasurable.mul (Lp.aestronglyMeasurable f))
  filter_upwards [] with p
  change ‖K p * f p‖ ≤ M.val * ‖f p‖
  rw [norm_mul, Real.norm_eq_abs (K p)]
  exact mul_le_mul_of_nonneg_right (hb p) (norm_nonneg _)

def brownianAdaptedContinuousMultiplierValue (hK : Measurable K)
    (hb : ∀ p, |K p| ≤ M.val) (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
  (brownianAdaptedContinuousMultiplier_memLp hK hb f).toLp (fun p => K p * f p)

theorem brownianAdaptedContinuousMultiplierValue_coe (hK : Measurable K)
    (hb : ∀ p, |K p| ≤ M.val) (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    brownianAdaptedContinuousMultiplierValue hK hb f =ᵐ[volume.prod P] (fun p => K p * f p) :=
  (brownianAdaptedContinuousMultiplier_memLp hK hb f).coeFn_toLp

theorem brownianAdaptedContinuousMultiplierValue_norm (hK : Measurable K)
    (hb : ∀ p, |K p| ≤ M.val) (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    ‖brownianAdaptedContinuousMultiplierValue hK hb f‖ ≤ M.val * ‖f‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [brownianAdaptedContinuousMultiplierValue_coe hK hb f] with p hp
  rw [hp, norm_mul, Real.norm_eq_abs (K p)]
  exact mul_le_mul_of_nonneg_right (hb p) (norm_nonneg _)

def brownianAdaptedContinuousMultiplierLinear (hK : Measurable K)
    (hb : ∀ p, |K p| ≤ M.val) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P) →ₗ[ℝ] Lp ℝ 2 ((volume : Measure ℝ).prod P) where
  toFun := brownianAdaptedContinuousMultiplierValue hK hb
  map_add' f g := by
    apply Lp.ext
    filter_upwards [brownianAdaptedContinuousMultiplierValue_coe hK hb (f + g),
      brownianAdaptedContinuousMultiplierValue_coe hK hb f,
      brownianAdaptedContinuousMultiplierValue_coe hK hb g,
      Lp.coeFn_add f g, Lp.coeFn_add (brownianAdaptedContinuousMultiplierValue hK hb f)
        (brownianAdaptedContinuousMultiplierValue hK hb g)] with p hsum hf hg hfg hout
    rw [hsum, hout, Pi.add_apply, hf, hg, hfg, Pi.add_apply, mul_add]
  map_smul' c f := by
    change brownianAdaptedContinuousMultiplierValue hK hb (c • f) =
      c • brownianAdaptedContinuousMultiplierValue hK hb f
    apply Lp.ext
    filter_upwards [brownianAdaptedContinuousMultiplierValue_coe hK hb (c • f),
      brownianAdaptedContinuousMultiplierValue_coe hK hb f, Lp.coeFn_smul c f,
      Lp.coeFn_smul c (brownianAdaptedContinuousMultiplierValue hK hb f)] with p hprod hf hcf hout
    rw [hprod, hout, Pi.smul_apply, hf, hcf, Pi.smul_apply]
    simp only [smul_eq_mul]
    ring

def brownianAdaptedContinuousMultiplierAmbient (hK : Measurable K)
    (hb : ∀ p, |K p| ≤ M.val) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P) →L[ℝ] Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
  (brownianAdaptedContinuousMultiplierLinear hK hb).mkContinuous M.val
    (brownianAdaptedContinuousMultiplierValue_norm hK hb)

theorem brownianAdaptedContinuousMultiplierAmbient_coe (hK : Measurable K)
    (hb : ∀ p, |K p| ≤ M.val) (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    brownianAdaptedContinuousMultiplierAmbient hK hb f =ᵐ[volume.prod P] (fun p => K p * f p) :=
  brownianAdaptedContinuousMultiplierValue_coe hK hb f

theorem brownianAdaptedContinuousMultiplierAmbient_norm (hK : Measurable K)
    (hb : ∀ p, |K p| ≤ M.val) (f : Lp ℝ 2 ((volume : Measure ℝ).prod P)) :
    ‖brownianAdaptedContinuousMultiplierAmbient hK hb f‖ ≤ M.val * ‖f‖ :=
  brownianAdaptedContinuousMultiplierValue_norm hK hb f

end TimeTraps.Probability

end
