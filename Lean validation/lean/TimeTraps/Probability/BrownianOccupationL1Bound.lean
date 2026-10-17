module

public import TimeTraps.Probability.BrownianOccupationL1Integrability

@[expose] public section

/-! An actual L1 bound for ordinary Brownian occupation time, obtained
from one-time Gaussian densities and Fubini. The coefficient is the exact
integral of (2 pi s)^(-1/2); the formula includes T=0. No occupation
formula, transition density, or boundedness of the scalar L1 test is assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianItoDrift_L1_integrable (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g) : Integrable (brownianItoDrift B g T) P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have he : brownianItoDrift B g T =
      (fun ω => ∫ s in Ioc (0 : ℝ) T.val, g (B s.toNNReal ω)) :=
    funext (fun _ => intervalIntegral.integral_of_le T.coe_nonneg)
  rw [he]
  exact (brownian_time_L1_integrable hB hjoint T hg).integral_prod_right

theorem brownian_absolute_occupation_mean_bound (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g) :
    (∫ ω, brownianItoDrift B (fun x => |g x|) T ω ∂P) ≤
      (2 * Real.sqrt T.val / Real.sqrt (2 * Real.pi)) * ∫ x, |g x| := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hi : Integrable (fun p : ℝ × Ω => |g (B p.1.toNNReal p.2)|)
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod P) := by
    simpa only [Real.norm_eq_abs] using (brownian_time_L1_integrable hB hjoint T hg).norm
  have hdom := ((intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mp
    (brownianOccupationL1Majorant_intervalIntegrable T.val)).mul_const (∫ x, |g x|)
  calc
    _ = ∫ s in Ioc (0 : ℝ) T.val, ∫ ω, |g (B s.toNNReal ω)| ∂P := by
      have he : brownianItoDrift B (fun x => |g x|) T =
          (fun ω => ∫ s in Ioc (0 : ℝ) T.val, |g (B s.toNNReal ω)|) :=
        funext (fun _ => intervalIntegral.integral_of_le T.coe_nonneg)
      rw [he]
      exact (integral_integral_swap (f := fun (s : ℝ) (ω : Ω) => |g (B s.toNNReal ω)|) hi).symm
    _ ≤ ∫ s in Ioc (0 : ℝ) T.val, brownianOccupationL1Majorant s * (∫ x, |g x|) := by
      apply integral_mono_ae hi.integral_prod_left hdom
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [brownianOccupationL1Majorant_eq_peak hs.1.le]
      have hb := brownian_eval_L1_abs_bound hB hg (Real.toNNReal_pos.mpr hs.1)
      simpa only [Real.coe_toNNReal s hs.1.le] using hb
    _ = _ := by
      have hm : (∫ s in Ioc (0 : ℝ) T.val, brownianOccupationL1Majorant s) =
          2 * Real.sqrt T.val / Real.sqrt (2 * Real.pi) :=
        (intervalIntegral.integral_of_le T.coe_nonneg).symm.trans
          (brownianOccupationL1Majorant_integral T.val)
      rw [integral_mul_const, hm]

theorem brownianItoDrift_L1_mean_abs_bound (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g) :
    (∫ ω, |brownianItoDrift B g T ω| ∂P) ≤
      (2 * Real.sqrt T.val / Real.sqrt (2 * Real.pi)) * ∫ x, |g x| := by
  have hgn : Integrable (fun x => |g x|) := by simpa only [Real.norm_eq_abs] using hg.norm
  calc
    _ ≤ ∫ ω, brownianItoDrift B (fun x => |g x|) T ω ∂P := by
      apply integral_mono (brownianItoDrift_L1_integrable hB hjoint T hg).norm
        (brownianItoDrift_L1_integrable hB hjoint T hgn)
      intro ω
      exact intervalIntegral.abs_integral_le_integral_abs T.coe_nonneg
    _ ≤ _ := brownian_absolute_occupation_mean_bound hB hjoint T hg

theorem brownianDyadic_absolute_occupation_mean_bound (T : ℝ≥0)
    {g : ℝ → ℝ} (hg : Integrable g) :
    (∫ ω, brownianItoDrift brownianDyadicPath (fun x => |g x|) T ω ∂brownianDyadicMeasure) ≤
      (2 * Real.sqrt T.val / Real.sqrt (2 * Real.pi)) * ∫ x, |g x| :=
  brownian_absolute_occupation_mean_bound brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_jointly_measurable T hg

theorem brownianItoDrift_L1_difference_bound (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0)
    {g k : ℝ → ℝ} (hg : Integrable g) (hk : Integrable k) :
    (∫ ω, |brownianItoDrift B g T ω - brownianItoDrift B k T ω| ∂P) ≤
      (2 * Real.sqrt T.val / Real.sqrt (2 * Real.pi)) * ∫ x, |g x - k x| := by
  have he : (fun ω => brownianItoDrift B g T ω - brownianItoDrift B k T ω) =ᵐ[P]
      brownianItoDrift B (fun x => g x - k x) T := by
    filter_upwards [brownian_time_L1_intervalIntegrable_ae hB hjoint T hg,
      brownian_time_L1_intervalIntegrable_ae hB hjoint T hk] with ω hωg hωk
    exact (intervalIntegral.integral_sub hωg hωk).symm
  calc
    _ = ∫ ω, |brownianItoDrift B (fun x => g x - k x) T ω| ∂P :=
      integral_congr_ae (he.fun_comp abs)
    _ ≤ _ := brownianItoDrift_L1_mean_abs_bound hB hjoint T (hg.sub hk)

end TimeTraps.Probability
