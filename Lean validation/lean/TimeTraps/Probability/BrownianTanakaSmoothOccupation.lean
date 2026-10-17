module

public import TimeTraps.Analysis.TanakaOccupationKernelFubini
public import TimeTraps.Probability.BrownianTanakaCompensation
public import TimeTraps.Probability.BrownianOccupationTimeBound

@[expose] public section

/-! The actual smooth Tanaka correction is the ordinary time integral
of the half-second-derivative kernel. This drift is jointly measurable
in level and sample point and uniformly bounded on finite horizons.
The bounds and measurability require no Brownian law. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaKernelDrift_joint_measurable {ε : ℝ} (hε : 0 < ε)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Measurable (fun p : ℝ × Ω =>
      brownianItoDrift B (fun x => tanakaOccupationKernel ε (x - p.1)) T p.2) := by
  have hj : Measurable (fun p : ℝ≥0 × (ℝ × Ω) => B p.1 p.2.2 - p.2.1) :=
    (hjoint.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).sub
      (measurable_fst.comp measurable_snd)
  exact brownianItoDrift_bounded_measurable
    (B := fun t (p : ℝ × Ω) => B t p.2 - p.1)
    (tanakaOccupationKernel_continuous hε).measurable hj T

theorem brownianTanakaKernelDrift_abs_bound {ε : ℝ} (hε : 0 < ε)
    (a : ℝ) (T : ℝ≥0) (ω : Ω) :
    |brownianItoDrift B (fun x => tanakaOccupationKernel ε (x - a)) T ω| ≤ T.val / (2 * ε) := by
  calc
    _ ≤ T.val * (1 / (2 * ε)) := brownianItoDrift_bounded_abs
      (fun x => by
        rw [abs_of_nonneg (tanakaOccupationKernel_nonneg hε (x - a))]
        exact tanakaOccupationKernel_uniform_bound hε (x - a)) T ω
    _ = _ := by ring

theorem brownianTanakaSmoothCompensation_kernel_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    brownianTanakaSmoothCompensation hB hBm hjoint a T n =ᵐ[P]
      (fun ω => brownianItoDrift B
        (fun x => tanakaOccupationKernel (tanakaSmoothingScale n) (x - a)) T ω) := by
  filter_upwards [brownianTanakaSmoothCompensation_coe hB hBm hjoint a T n] with ω hω
  rw [hω]
  unfold brownianItoDrift
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro s _
  change (1 / 2 : ℝ) * deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) a))
    (B s.toNNReal ω) = tanakaOccupationKernel (tanakaSmoothingScale n) (B s.toNNReal ω - a)
  rw [tanakaSmoothShift_second_deriv,
    tanakaOccupationKernel_eq_half_second (tanakaSmoothingScale_pos n)]

end TimeTraps.Probability
