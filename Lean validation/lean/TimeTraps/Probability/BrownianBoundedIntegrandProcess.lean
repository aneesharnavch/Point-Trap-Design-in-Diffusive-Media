module

public import TimeTraps.Probability.BrownianSignIntegrandProcess

@[expose] public section

/-! Measurable bounded scalar functions give actual finite-horizon product-L²
processes. This analytic statement needs only a finite path measure and joint
measurability, not membership in the stochastic-integrand domain. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianBoundedProcess (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) : ℝ × Ω → ℝ :=
  brownianSquareProcess (fun t ω => g (B t ω)) T

theorem brownianBoundedProcess_measurable {g : ℝ → ℝ} (hg : Measurable g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Measurable (brownianBoundedProcess B g T) :=
  brownianSquareProcess_measurable (hg.comp hjoint) T

theorem brownianBoundedProcess_abs_le (B : ℝ≥0 → Ω → ℝ) {g : ℝ → ℝ} {M : ℝ}
    (hb : ∀ x, |g x| ≤ M) (T : ℝ≥0) (p : ℝ × Ω) :
    |brownianBoundedProcess B g T p| ≤ M * brownianIntervalIndicator 0 T p.1 := by
  change |(Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * g (B p.1.toNNReal p.2)| ≤
    M * (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · simpa only [Set.indicator_of_mem hp, one_mul, mul_one] using hb (B p.1.toNNReal p.2)
  · simp only [Set.indicator_of_notMem hp, zero_mul, mul_zero, abs_zero, le_refl]

theorem brownianBoundedProcess_memLp [IsFiniteMeasure P] {g : ℝ → ℝ} {M : ℝ}
    (hg : Measurable g) (hb : ∀ x, |g x| ≤ M)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    MemLp (brownianBoundedProcess B g T) 2 ((volume : Measure ℝ).prod P) := by
  apply (brownianElementaryProcess_memLp (P := P) 0 T measurable_const (memLp_const M)).mono'
    (brownianBoundedProcess_measurable hg hjoint T).aestronglyMeasurable
  filter_upwards [] with p
  simpa only [brownianElementaryProcess, Real.norm_eq_abs, mul_comm] using
    brownianBoundedProcess_abs_le B hb T p

noncomputable def brownianBoundedProcessL2 (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ) (T : ℝ≥0)
    (hg : MemLp (brownianBoundedProcess B g T) 2 ((volume : Measure ℝ).prod P)) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P) := hg.toLp (brownianBoundedProcess B g T)

theorem brownianBoundedProcessL2_coe (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ) (T : ℝ≥0)
    (hg : MemLp (brownianBoundedProcess B g T) 2 ((volume : Measure ℝ).prod P)) :
    brownianBoundedProcessL2 B g T hg =ᵐ[volume.prod P] brownianBoundedProcess B g T :=
  hg.coeFn_toLp

theorem brownianBoundedProcess_error_le (B : ℝ≥0 → Ω → ℝ) {g h : ℝ → ℝ} {M : ℝ}
    (hg : ∀ x, |g x| ≤ M) (hh : ∀ x, |h x| ≤ M) (T : ℝ≥0) (p : ℝ × Ω) :
    (brownianBoundedProcess B g T p - brownianBoundedProcess B h T p) ^ 2 ≤
      (2 * M) ^ 2 * brownianIntervalIndicator 0 T p.1 := by
  change ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * g (B p.1.toNNReal p.2) -
    (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * h (B p.1.toNNReal p.2)) ^ 2 ≤
      (2 * M) ^ 2 * (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · simp only [Set.indicator_of_mem hp, one_mul, mul_one]
    have he : |g (B p.1.toNNReal p.2) - h (B p.1.toNNReal p.2)| ≤ 2 * M :=
      (abs_sub _ _).trans (by linarith [hg (B p.1.toNNReal p.2), hh (B p.1.toNNReal p.2)])
    nlinarith [sq_nonneg (2 * M - |g (B p.1.toNNReal p.2) - h (B p.1.toNNReal p.2)|),
      abs_nonneg (g (B p.1.toNNReal p.2) - h (B p.1.toNNReal p.2)),
      sq_abs (g (B p.1.toNNReal p.2) - h (B p.1.toNNReal p.2))]
  · simp only [Set.indicator_of_notMem hp, zero_mul, mul_zero, sub_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), le_refl]

theorem brownianBoundedProcess_tendsto (B : ℝ≥0 → Ω → ℝ) {g : ℕ → ℝ → ℝ} {h : ℝ → ℝ}
    (hlim : ∀ x, Tendsto (fun n => g n x) atTop (𝓝 (h x))) (T : ℝ≥0) (p : ℝ × Ω) :
    Tendsto (fun n => brownianBoundedProcess B (g n) T p) atTop (𝓝 (brownianBoundedProcess B h T p)) :=
  (hlim (B p.1.toNNReal p.2)).const_mul ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1)

end TimeTraps.Probability
