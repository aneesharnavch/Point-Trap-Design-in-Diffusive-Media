module

public import TimeTraps.Probability.BrownianTanakaSmooth
public import TimeTraps.Probability.BrownianTanakaDifferenceConvergence
public import TimeTraps.Analysis.LpLimitNonnegative

@[expose] public section

/-! The actual L² limit of the nonnegative smooth Itô corrections.
The limit is identified with absolute Brownian displacement minus the
constructed sign integral; no temporal regularity is assumed here. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianTanakaCompensation (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) : Lp ℝ 2 P :=
  brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T) -
    brownianSignIntegral hB hBm hjoint a T

noncomputable def brownianTanakaSmoothCompensation (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ) : Lp ℝ 2 P :=
  brownianTanakaApproxDifferenceL2 B (tanakaSmoothShift (tanakaSmoothingScale n) a) T
    (brownianTanakaApproxDifference_memLp hB hBm
      (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a).continuous.measurable
      (tanakaSmoothShift_error (tanakaSmoothingScale_pos n).le a) T) -
    brownianTanakaSmoothIntegral hB hBm hjoint a T n

theorem brownianTanakaCompensation_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    brownianTanakaCompensation hB hBm hjoint a T =ᵐ[P]
      (fun ω => |B T ω - a| - |B 0 ω - a| - brownianSignIntegral hB hBm hjoint a T ω) := by
  filter_upwards [Lp.coeFn_sub (brownianTanakaDifferenceL2 B a T
    (brownianTanakaDifference_memLp hB a T)) (brownianSignIntegral hB hBm hjoint a T),
    brownianTanakaDifferenceL2_coe B a T (brownianTanakaDifference_memLp hB a T)] with ω hd ha
  change (brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T) -
    brownianSignIntegral hB hBm hjoint a T) ω = _
  rw [hd, Pi.sub_apply, ha]
  rfl

theorem brownianTanakaSmoothCompensation_coe (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    brownianTanakaSmoothCompensation hB hBm hjoint a T n =ᵐ[P]
      (fun ω => (1 / 2 : ℝ) * brownianItoDrift B
        (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) a))) T ω) := by
  let F := tanakaSmoothShift (tanakaSmoothingScale n) a
  let hM := brownianTanakaApproxDifference_memLp hB hBm
    (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a).continuous.measurable
    (tanakaSmoothShift_error (tanakaSmoothingScale_pos n).le a) T
  let A := brownianTanakaApproxDifferenceL2 B F T hM
  let I := brownianTanakaSmoothIntegral hB hBm hjoint a T n
  filter_upwards [Lp.coeFn_sub A I, brownianTanakaApproxDifferenceL2_coe B F T hM,
    brownianTanakaSmooth_formula hB hBm hjoint a T n] with ω hd ha hi
  change (A - I) ω = _
  rw [hd, Pi.sub_apply, ha]
  change F (B T ω) - F (B 0 ω) - I ω = _
  change F (B T ω) - F (B 0 ω) = I ω + _ at hi
  linarith

theorem brownianTanakaSmoothCompensation_tendsto (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    Tendsto (brownianTanakaSmoothCompensation hB hBm hjoint a T) atTop
      (𝓝 (brownianTanakaCompensation hB hBm hjoint a T)) :=
  brownianTanakaCompensation_tendsto hB hBm hjoint
    (fun n => (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) a).continuous.measurable)
    (fun n => (tanakaSmoothingScale_pos n).le)
    (fun n => tanakaSmoothShift_error (tanakaSmoothingScale_pos n).le a)
    tanakaSmoothingScale_tendsto T _ (brownianTanakaSmoothIntegral_tendsto hB hBm hjoint a T)

theorem brownianTanakaSmoothCompensation_nonneg (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ) :
    ∀ᵐ ω ∂P, 0 ≤ brownianTanakaSmoothCompensation hB hBm hjoint a T n ω := by
  filter_upwards [brownianTanakaSmoothCompensation_coe hB hBm hjoint a T n] with ω hω
  rw [hω]
  exact brownianTanakaSmooth_drift_nonneg B a T n ω

theorem brownianTanakaCompensation_nonneg (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, 0 ≤ brownianTanakaCompensation hB hBm hjoint a T ω :=
  ae_nonnegative_of_L2_tendsto _ _ (brownianTanakaSmoothCompensation_tendsto hB hBm hjoint a T)
    (brownianTanakaSmoothCompensation_nonneg hB hBm hjoint a T)

end TimeTraps.Probability
