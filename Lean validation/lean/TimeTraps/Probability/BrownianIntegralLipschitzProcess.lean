module

public import TimeTraps.Probability.BrownianIntegralSquareProcess
public import TimeTraps.Probability.BrownianIntegralSquareApproximation

@[expose] public section

/-! Actual finite-horizon Lipschitz functions of Brownian motion in
product L². Centering g at zero allows a nonzero g(0), which is retained
as a finite-horizon constant elementary process. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem brownianLipschitz_centered {g : ℝ → ℝ} {K : ℝ≥0} (hg : LipschitzWith K g) :
    LipschitzWith K (fun x => g x - g 0) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  have he : (g x - g 0) - (g y - g 0) = g x - g y := by ring
  simpa only [Real.dist_eq, he] using hg.dist_le_mul x y

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {K : ℝ≥0}

theorem brownianLipschitz_eval_memLp (hB : IsPreBrownianReal B P) (hg : LipschitzWith K g) (t : ℝ≥0) :
    MemLp (fun ω => g (B t ω)) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hc := (brownianLipschitz_centered hg).comp_memLp (by simp)
    (hB.hasLaw_eval t).hasGaussianLaw.memLp_two
  convert hc.add (memLp_const (g 0)) using 1
  funext ω
  simp

noncomputable def brownianLipschitzProcess (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) : ℝ × Ω → ℝ :=
  brownianSquareProcess (fun t ω => g (B t ω)) T

theorem brownianLipschitzProcess_measurable (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Measurable (brownianLipschitzProcess B g T) :=
  brownianSquareProcess_measurable (hg.continuous.measurable.comp hjoint) T

theorem brownianLipschitzProcess_memLp (hB : IsPreBrownianReal B P) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    MemLp (brownianLipschitzProcess B g T) 2 (volume.prod P) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hc := (brownianLipschitz_centered hg).comp_memLp (by simp)
    (brownianSquareProcess_memLp hB hjoint T)
  have hk := brownianElementaryProcess_memLp (P := P) 0 T measurable_const (memLp_const (g 0))
  convert hc.add hk using 1
  funext p
  change (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * g (B p.1.toNNReal p.2) =
    g ((Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * B p.1.toNNReal p.2) - g 0 +
      (Ioc (0 : ℝ) T.val).indicator (fun _ => 1) p.1 * g 0
  by_cases hp : p.1 ∈ Ioc (0 : ℝ) T.val
  · simp only [Set.indicator_of_mem hp, one_mul, sub_add_cancel]
  · simp only [Set.indicator_of_notMem hp, zero_mul, sub_self, add_zero]

noncomputable def brownianLipschitzProcessL2 (hB : IsPreBrownianReal B P) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Lp ℝ 2 ((volume : Measure ℝ).prod P) :=
  (brownianLipschitzProcess_memLp hB hg hjoint T).toLp (brownianLipschitzProcess B g T)

theorem brownianLipschitzProcessL2_coe (hB : IsPreBrownianReal B P) (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    brownianLipschitzProcessL2 hB hg hjoint T =ᵐ[volume.prod P] brownianLipschitzProcess B g T :=
  (brownianLipschitzProcess_memLp hB hg hjoint T).coeFn_toLp

end TimeTraps.Probability
