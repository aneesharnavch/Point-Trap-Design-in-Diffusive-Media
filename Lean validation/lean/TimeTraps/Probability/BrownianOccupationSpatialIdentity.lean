module

public import TimeTraps.Probability.BrownianLocalTimeSmoothIntegral
public import TimeTraps.Probability.BrownianTanakaSmoothOccupation
public import TimeTraps.Probability.BrownianOccupationTimeKernel
public import TimeTraps.Analysis.L2IntegralSections

@[expose] public section

/-! Spatially integrating the actual smooth Tanaka corrections gives
the L2 class of the genuine kernel-averaged time integral. Fubini is
justified at the measurable kernel sections and transported by Hilbert
duality; no jointly selected pointwise local-time version is assumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaSmoothLevelIntegral_eq_kernelTime (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    {g : ℝ → ℝ} (hg : Integrable g) (hgm : Measurable g) {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) (n : ℕ) :
    brownianTanakaSmoothLevelIntegral hB hBm hjoint T g n =
      brownianItoDriftL2 B
        (fun x => ∫ y, tanakaOccupationKernel (tanakaSmoothingScale n) y * g (x - y)) T
        (by
          have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
          exact brownianOccupationKernel_time_memLp (P := P)
            (tanakaSmoothingScale_pos n) hgm hjoint hb T) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let ε := tanakaSmoothingScale n
  have hε : 0 < ε := tanakaSmoothingScale_pos n
  let K : ℝ × Ω → ℝ := fun p =>
    brownianItoDrift B (fun x => tanakaOccupationKernel ε (x - p.1)) T p.2
  have hK : Measurable K := brownianTanakaKernelDrift_joint_measurable hε hjoint T
  apply real_L2_integral_eq_sections
    (brownianTanakaSmoothCompensation_weight_integrable hB hBm hjoint T n hg)
    (f := fun p => g p.1 * K p)
    (hg.aestronglyMeasurable.comp_fst.mul hK.aestronglyMeasurable)
  · intro a
    filter_upwards [Lp.coeFn_smul (g a) (brownianTanakaSmoothCompensation hB hBm hjoint a T n),
      brownianTanakaSmoothCompensation_kernel_coe hB hBm hjoint a T n] with ω hs hk
    rw [hs, Pi.smul_apply, smul_eq_mul, hk]
  · filter_upwards [brownianItoDriftL2_coe B
      (fun x => ∫ y, tanakaOccupationKernel ε y * g (x - y)) T
      (brownianOccupationKernel_time_memLp (P := P) hε hgm hjoint hb T)] with ω hω
    rw [hω]
    have hpath : Measurable (fun s : ℝ => B s.toNNReal ω) :=
      hjoint.comp ((by fun_prop : Measurable (fun s : ℝ => s.toNNReal)).prodMk measurable_const)
    exact (tanakaOccupationKernel_time_fubini hε T.coe_nonneg hpath hg).symm
  · exact hg.norm.mul_const (T.val / (2 * ε))
  · filter_upwards [] with p
    change |g p.1 * K p| ≤ ‖g p.1‖ * (T.val / (2 * ε))
    rw [abs_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (brownianTanakaKernelDrift_abs_bound hε p.1 T p.2) (abs_nonneg _)

end TimeTraps.Probability
