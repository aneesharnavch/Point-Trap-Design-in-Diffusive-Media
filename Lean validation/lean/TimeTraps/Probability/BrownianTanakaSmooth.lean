module

public import TimeTraps.Analysis.TanakaSmoothAbsoluteLimit
public import TimeTraps.Probability.BrownianItoFormula
public import TimeTraps.Probability.BrownianSignIntegrandLimit

@[expose] public section

/-! Apply the proved C³ Itô formula to actual smooth absolute values.
The stochastic terms converge to the constructed sign integral, and
each ordinary drift correction is nonnegative. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

noncomputable def tanakaSmoothSecondBound (n : ℕ) : ℝ≥0 :=
  ⟨1 / tanakaSmoothingScale n, (one_div_pos.mpr (tanakaSmoothingScale_pos n)).le⟩

noncomputable def tanakaSmoothThirdBound (n : ℕ) : ℝ≥0 :=
  ⟨3 / tanakaSmoothingScale n ^ 2, div_nonneg (by norm_num) (sq_nonneg _)⟩

theorem brownianTanakaSmooth_second_bound (n : ℕ) (a x : ℝ) :
    |deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) a)) x| ≤
      (tanakaSmoothSecondBound n).val :=
  tanakaSmoothShift_second_bound (tanakaSmoothingScale_pos n) a x

theorem brownianTanakaSmooth_third_bound (n : ℕ) (a x : ℝ) :
    |iteratedDeriv 3 (tanakaSmoothShift (tanakaSmoothingScale n) a) x| ≤
      (tanakaSmoothThirdBound n).val :=
  tanakaSmoothShift_third_bound (tanakaSmoothingScale_pos n) a x

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianTanakaSmoothIntegral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ) : Lp ℝ 2 P :=
  brownianIntegral hB (brownianItoIntegrand hB hBm
    (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a)
    (brownianTanakaSmooth_second_bound n a) hjoint T)

theorem brownianTanakaSmoothIntegral_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    Tendsto (brownianTanakaSmoothIntegral hB hBm hjoint a T) atTop
      (𝓝 (brownianSignIntegral hB hBm hjoint a T)) :=
  brownianSignIntegral_general_tendsto hB hBm hjoint
    (fun n => brownianIto_firstDerivative_lipschitz
      (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a)
      (brownianTanakaSmooth_second_bound n a))
    (fun n x => tanakaSmoothShift_first_bound (tanakaSmoothingScale_pos n) a x)
    (tanakaSmoothShift_deriv_tendsto a) T

theorem brownianTanakaSmooth_formula (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    (fun ω => tanakaSmoothShift (tanakaSmoothingScale n) a (B T ω) -
      tanakaSmoothShift (tanakaSmoothingScale n) a (B 0 ω)) =ᵐ[P]
      (fun ω => brownianTanakaSmoothIntegral hB hBm hjoint a T n ω +
        (1 / 2 : ℝ) * brownianItoDrift B
          (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) a))) T ω) :=
  brownianIto_formula hB hBm (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a)
    (brownianTanakaSmooth_second_bound n a) (brownianTanakaSmooth_third_bound n a) hjoint T

theorem brownianTanakaSmooth_drift_nonneg (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    0 ≤ (1 / 2 : ℝ) * brownianItoDrift B
      (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) a))) T ω := by
  apply mul_nonneg (by norm_num)
  apply intervalIntegral.integral_nonneg_of_forall T.property
  intro s
  exact tanakaSmoothShift_second_nonneg (tanakaSmoothingScale_pos n) a (B s.toNNReal ω)

end TimeTraps.Probability
