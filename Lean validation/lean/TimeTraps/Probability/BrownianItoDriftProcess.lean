module

public import TimeTraps.Probability.BrownianItoDriftBound
public import TimeTraps.Probability.BrownianIntegralLipschitzApproximation

@[expose] public section

/-! The actual ordinary time integral of a globally Lipschitz function
of Brownian motion, with its product-L² and random-variable representatives. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}
variable {g : ℝ → ℝ} {K : ℝ≥0}

noncomputable def brownianItoDrift (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (ω : Ω) : ℝ := ∫ s in (0 : ℝ)..T.val, g (B s.toNNReal ω)

theorem brownianItoDrift_process_integral (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ)
    (T : ℝ≥0) (ω : Ω) :
    (∫ s in (0 : ℝ)..T.val, brownianLipschitzProcess B g T (s, ω)) = brownianItoDrift B g T ω := by
  calc
    _ = ∫ s in Ioc (0 : ℝ) T.val, brownianLipschitzProcess B g T (s, ω) :=
      intervalIntegral.integral_of_le T.coe_nonneg
    _ = ∫ s in Ioc (0 : ℝ) T.val, g (B s.toNNReal ω) := by
      apply setIntegral_congr_fun measurableSet_Ioc
      intro s hs
      simp only [brownianLipschitzProcess, brownianSquareProcess, Set.indicator_of_mem hs, one_mul]
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem brownianItoDrift_measurable (hg : LipschitzWith K g)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    Measurable (brownianItoDrift B g T) := by
  have hm : Measurable (fun p : ℝ × Ω => g (B p.1.toNNReal p.2)) :=
    hg.continuous.measurable.comp
      (hjoint.comp ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd))
  have he : brownianItoDrift B g T = (fun ω => ∫ s in Ioc (0 : ℝ) T.val, g (B s.toNNReal ω)) :=
    funext (fun _ => intervalIntegral.integral_of_le T.coe_nonneg)
  rw [he]
  exact (hm.stronglyMeasurable.integral_prod_left' (μ := volume.restrict (Ioc (0 : ℝ) T.val))).measurable

theorem brownianItoDrift_intervalIntegrable_ae (hB : IsPreBrownianReal B P)
    (hg : LipschitzWith K g) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, IntervalIntegrable (fun s => g (B s.toNNReal ω)) volume 0 T.val := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  filter_upwards [brownian_timeIntegral_sections (brownianLipschitzProcess_memLp hB hg hjoint T) T.val]
    with ω hω
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr
  apply hω.congr
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simp only [brownianLipschitzProcess, brownianSquareProcess, Set.indicator_of_mem hs, one_mul]

theorem brownianItoDrift_memLp (hB : IsPreBrownianReal B P)
    (hg : LipschitzWith K g) (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (T : ℝ≥0) :
    MemLp (brownianItoDrift B g T) 2 P := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  simpa only [brownianItoDrift_process_integral] using
    brownian_timeIntegral_memLp (brownianLipschitzProcess_memLp hB hg hjoint T) T.val T.coe_nonneg

noncomputable def brownianItoDriftL2 (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ) (T : ℝ≥0)
    (hDrift : MemLp (brownianItoDrift B g T) 2 P) : Lp ℝ 2 P :=
  hDrift.toLp (brownianItoDrift B g T)

theorem brownianItoDriftL2_coe (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ) (T : ℝ≥0)
    (hDrift : MemLp (brownianItoDrift B g T) 2 P) :
    brownianItoDriftL2 B g T hDrift =ᵐ[P] brownianItoDrift B g T := hDrift.coeFn_toLp

theorem brownianItoDriftL2_norm_sq (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ) (T : ℝ≥0)
    (hDrift : MemLp (brownianItoDrift B g T) 2 P) :
    ‖brownianItoDriftL2 B g T hDrift‖ ^ 2 = ∫ ω, brownianItoDrift B g T ω ^ 2 ∂P :=
  TimeTraps.Analysis.memLp_norm_toLp_sq hDrift

theorem brownianItoDrift_zero (B : ℝ≥0 → Ω → ℝ) (g : ℝ → ℝ) (ω : Ω) :
    brownianItoDrift B g 0 ω = 0 := by simp [brownianItoDrift]

end TimeTraps.Probability
