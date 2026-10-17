module

public import TimeTraps.Probability.OccupationProductOrder

@[expose] public section

/-! Genuine product integrability and Fubini for signed bounded scalar
occupation integrands. Only joint measurability is needed; continuity of
a stochastic process is not used as a substitute for product measurability. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter

variable {Ω : Type*} [MeasurableSpace Ω]

theorem occupationProduct_joint_integrable (μ : Measure Ω) (ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (F G : ℝ → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    {B C : ℝ} (hB : ∀ s ω, ‖F s ω‖ ≤ B) (hC : ∀ s ω, ‖G s ω‖ ≤ C) :
    Integrable (fun p : (ℝ × ℝ) × Ω => F p.1.1 p.2 * G p.1.2 p.2) ((ν.prod ν).prod μ) := by
  have hm : Measurable (fun p : (ℝ × ℝ) × Ω => F p.1.1 p.2 * G p.1.2 p.2) :=
    (hF.comp ((measurable_fst.fst).prodMk measurable_snd)).mul
      (hG.comp ((measurable_fst.snd).prodMk measurable_snd))
  apply (integrable_const (B * C)).mono' hm.aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  rw [norm_mul]
  exact mul_le_mul (hB _ _) (hC _ _) (norm_nonneg _) ((norm_nonneg (F p.1.1 p.2)).trans (hB p.1.1 p.2))

theorem occupationProduct_mean_integrable (μ : Measure Ω) (ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (F G : ℝ → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    {B C : ℝ} (hB : ∀ s ω, ‖F s ω‖ ≤ B) (hC : ∀ s ω, ‖G s ω‖ ≤ C) :
    Integrable (fun p : ℝ × ℝ => ∫ ω, F p.1 ω * G p.2 ω ∂μ) (ν.prod ν) :=
  (occupationProduct_joint_integrable μ ν F G hF hG hB hC).integral_prod_left

theorem occupationProduct_integrable (μ : Measure Ω) (ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (F G : ℝ → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    {B C : ℝ} (hB : ∀ s ω, ‖F s ω‖ ≤ B) (hC : ∀ s ω, ‖G s ω‖ ≤ C) :
    Integrable (fun ω => (∫ s, F s ω ∂ν) * ∫ t, G t ω ∂ν) μ := by
  have hi := (occupationProduct_joint_integrable μ ν F G hF hG hB hC).integral_prod_right
  exact hi.congr (Eventually.of_forall (fun ω => integral_prod_mul (F · ω) (G · ω)))

theorem occupationProduct_expectation (μ : Measure Ω) (ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (F G : ℝ → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    {B C : ℝ} (hB : ∀ s ω, ‖F s ω‖ ≤ B) (hC : ∀ s ω, ‖G s ω‖ ≤ C) :
    (∫ ω, (∫ s, F s ω ∂ν) * (∫ t, G t ω ∂ν) ∂μ) =
      ∫ p : ℝ × ℝ, ∫ ω, F p.1 ω * G p.2 ω ∂μ ∂ν.prod ν := by
  calc
    _ = ∫ ω, ∫ p : ℝ × ℝ, F p.1 ω * G p.2 ω ∂ν.prod ν ∂μ :=
      integral_congr_ae (Eventually.of_forall (fun ω =>
        (integral_prod_mul (F · ω) (G · ω)).symm))
    _ = _ := (integral_integral_swap
      (occupationProduct_joint_integrable μ ν F G hF hG hB hC)).symm

theorem occupationProduct_expectation_ordered (μ : Measure Ω) (ν : Measure ℝ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] [NullSingletonClass ν]
    (F G : ℝ → Ω → ℝ)
    (hF : Measurable (Function.uncurry F)) (hG : Measurable (Function.uncurry G))
    {B C : ℝ} (hB : ∀ s ω, ‖F s ω‖ ≤ B) (hC : ∀ s ω, ‖G s ω‖ ≤ C) :
    (∫ ω, (∫ s, F s ω ∂ν) * (∫ t, G t ω ∂ν) ∂μ) =
      orderedTimeIntegral ν (fun p => ∫ ω, F p.1 ω * G p.2 ω ∂μ) +
      orderedTimeIntegral ν (fun p => ∫ ω, G p.1 ω * F p.2 ω ∂μ) := by
  rw [occupationProduct_expectation μ ν F G hF hG hB hC]
  have he := integral_timeSquare_eq_ordered ν
    (occupationProduct_mean_integrable μ ν F G hF hG hB hC)
  simpa only [Function.comp_def, Prod.fst_swap, Prod.snd_swap, mul_comm] using he

end TimeTraps.Probability
