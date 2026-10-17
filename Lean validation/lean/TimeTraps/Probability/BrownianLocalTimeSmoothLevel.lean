module

public import TimeTraps.Probability.BrownianLocalTimeSmoothNorm
public import TimeTraps.Probability.BrownianOccupationTimeConvergence

@[expose] public section

/-! Each fixed smooth Tanaka compensation is continuous in its level
as an actual L²-valued function. The proof identifies it with half the
ordinary derivative drift in L², then uses bounded time-integral
convergence under translation. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaSmoothCompensation_eq_driftL2 (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) (n : ℕ)
    (hD : MemLp (brownianItoDrift B (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) a))) T) 2 P) :
    brownianTanakaSmoothCompensation hB hBm hjoint a T n =
      (1 / 2 : ℝ) • brownianItoDriftL2 B (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) a))) T hD := by
  apply Lp.ext
  filter_upwards [brownianTanakaSmoothCompensation_coe hB hBm hjoint a T n,
    Lp.coeFn_smul (1 / 2 : ℝ)
      (brownianItoDriftL2 B (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) a))) T hD),
    brownianItoDriftL2_coe B (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) a))) T hD]
    with ω hc hs hd
  rw [hc, hs, Pi.smul_apply, hd, smul_eq_mul]

theorem brownianTanakaSmoothCompensation_level_continuous (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) (n : ℕ) :
    Continuous (fun a => brownianTanakaSmoothCompensation hB hBm hjoint a T n) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hg (b : ℝ) : Measurable (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) b))) := by
    have h1 : ContDiff ℝ 2 (deriv (tanakaSmoothShift (tanakaSmoothingScale n) b)) :=
      (tanakaSmoothShift_contDiff (tanakaSmoothingScale_pos n) b).deriv'
    have h2 : ContDiff ℝ 1 (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) b))) := h1.deriv'
    exact h2.continuous.measurable
  have hc : Continuous (deriv (deriv (tanakaSmoothAbs (tanakaSmoothingScale n)))) := by
    have h1 : ContDiff ℝ 2 (deriv (tanakaSmoothAbs (tanakaSmoothingScale n))) :=
      (tanakaSmoothAbs_contDiff (tanakaSmoothingScale_pos n)).deriv'
    have h2 : ContDiff ℝ 1 (deriv (deriv (tanakaSmoothAbs (tanakaSmoothingScale n)))) := h1.deriv'
    exact h2.continuous
  let D (b : ℝ) := brownianItoDriftL2 B (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) b))) T
    (brownianItoDrift_bounded_memLp (P := P) (hg b) hjoint (brownianTanakaSmooth_second_bound n b) T)
  have he (b : ℝ) : (1 / 2 : ℝ) • D b = brownianTanakaSmoothCompensation hB hBm hjoint b T n :=
    (brownianTanakaSmoothCompensation_eq_driftL2 hB hBm hjoint b T n _).symm
  apply continuous_iff_seqContinuous.mpr
  intro u a hu
  change Tendsto (fun k => brownianTanakaSmoothCompensation hB hBm hjoint (u k) T n) atTop
    (𝓝 (brownianTanakaSmoothCompensation hB hBm hjoint a T n))
  have hlim (x : ℝ) :
      Tendsto (fun k => deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) (u k))) x) atTop
        (𝓝 (deriv (deriv (tanakaSmoothShift (tanakaSmoothingScale n) a)) x)) := by
    simp only [tanakaSmoothShift_second_deriv]
    exact hc.continuousAt.tendsto.comp (tendsto_const_nhds.sub hu)
  have hd : Tendsto (fun k => D (u k)) atTop (𝓝 (D a)) :=
    brownianItoDriftL2_bounded_tendsto (fun k => hg (u k)) (hg a) hjoint
      (fun k => brownianTanakaSmooth_second_bound n (u k))
      (brownianTanakaSmooth_second_bound n a) hlim T
  simpa only [he] using hd.const_smul (1 / 2 : ℝ)

end TimeTraps.Probability
