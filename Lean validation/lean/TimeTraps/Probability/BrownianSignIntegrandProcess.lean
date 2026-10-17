module

public import TimeTraps.Probability.BrownianSignIntegrandApproximation

@[expose] public section

/-! The actual bounded finite-horizon sign process and its L² representative.
Joint measurability and finite time support give square integrability. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianSignProcess (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0) : ℝ × Ω → ℝ :=
  brownianSquareProcess (fun t ω => Real.sign (B t ω - a)) T

theorem brownianSignProcess_measurable
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    Measurable (brownianSignProcess B a T) :=
  brownianSquareProcess_measurable (brownianSign_measurable.comp (hjoint.sub_const a)) T

theorem brownianSignProcess_abs_le (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0) (p : ℝ × Ω) :
    |brownianSignProcess B a T p| ≤ brownianIntervalIndicator 0 T p.1 := by
  change |(Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 *
      Real.sign (B p.1.toNNReal p.2 - a)| ≤ (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · simpa only [Set.indicator_of_mem hp, one_mul] using brownianSign_abs_le (B p.1.toNNReal p.2 - a)
  · simp only [Set.indicator_of_notMem hp, zero_mul, abs_zero, le_refl]

theorem brownianSignProcess_memLp (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    MemLp (brownianSignProcess B a T) 2 ((volume : Measure ℝ).prod P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  apply (brownianElementaryProcess_memLp (P := P) 0 T measurable_const (memLp_const (1 : ℝ))).mono'
    (brownianSignProcess_measurable hjoint a T).aestronglyMeasurable
  filter_upwards [] with p
  simpa only [brownianElementaryProcess, mul_one, Real.norm_eq_abs] using brownianSignProcess_abs_le B a T p

noncomputable def brownianSignProcessL2 (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0)
    (hSign : MemLp (brownianSignProcess B a T) 2 ((volume : Measure ℝ).prod P)) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P) := hSign.toLp (brownianSignProcess B a T)

theorem brownianSignProcessL2_coe (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (T : ℝ≥0)
    (hSign : MemLp (brownianSignProcess B a T) 2 ((volume : Measure ℝ).prod P)) :
    brownianSignProcessL2 B a T hSign =ᵐ[volume.prod P] brownianSignProcess B a T := hSign.coeFn_toLp

theorem brownianSignProcess_zero (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (p : ℝ × Ω) :
    brownianSignProcess B a 0 p = 0 := by simp [brownianSignProcess, brownianSquareProcess]

theorem brownianSignProcess_approximation_bound (B : ℝ≥0 → Ω → ℝ)
    (a : ℝ) (T : ℝ≥0) (n : ℕ) (p : ℝ × Ω) :
    (brownianLipschitzProcess B (brownianSignApprox a n) T p - brownianSignProcess B a T p) ^ 2 ≤
      4 * brownianIntervalIndicator 0 T p.1 := by
  change ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * brownianSignApprox a n (B p.1.toNNReal p.2) -
    (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * Real.sign (B p.1.toNNReal p.2 - a)) ^ 2 ≤
      4 * (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · simp only [Set.indicator_of_mem hp, one_mul, mul_one]
    have ha := abs_le.mp (brownianSignApprox_abs_le a n (B p.1.toNNReal p.2))
    have hs := abs_le.mp (brownianSign_abs_le (B p.1.toNNReal p.2 - a))
    nlinarith [ha.1, ha.2, hs.1, hs.2]
  · simp only [Set.indicator_of_notMem hp, zero_mul, mul_zero, sub_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), le_refl]

end TimeTraps.Probability
