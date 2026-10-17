module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemDynkin

@[expose] public section

/-! Discounted continuous observations of every competing process are
absolutely integrable on the full time/sample product and on each path.
Thus either order of expectation and infinite-time integration is valid. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium}
variable {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.discounted_observation_measurable
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (α : ℝ) :
    Measurable (fun p : ℝ × Ω => Real.exp (-α * p.1) * g (X p.1.toNNReal p.2)) := by
  have hm : Measurable (fun p : ℝ × Ω => g (X p.1.toNNReal p.2)) :=
    (h.observation_jointlyMeasurable hg).comp
      ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd)
  exact (by fun_prop : Measurable (fun p : ℝ × Ω => Real.exp (-α * p.1))).mul hm

theorem ReversibleNeumannMartingaleProblem.discounted_observation_path_integrable
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right))
    {α : ℝ} (hα : 0 < α) (ω : Ω) :
    IntegrableOn (fun t => Real.exp (-α * t) * g (X t.toNNReal ω)) (Ioi (0 : ℝ)) := by
  obtain ⟨M, _, hb⟩ := h.observation_bound hg
  apply ((exp_neg_integrableOn_Ioi 0 hα).mul_const M).mono'
    (((h.discounted_observation_measurable hg α).comp
      (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro t
  change ‖Real.exp (-α * t) * g (X t.toNNReal ω)‖ ≤ Real.exp (-α * t) * M
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb t.toNNReal ω) (Real.exp_pos _).le

theorem ReversibleNeumannMartingaleProblem.discounted_observation_joint_integrable [IsProbabilityMeasure μ]
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) {α : ℝ} (hα : 0 < α) :
    Integrable (fun p : ℝ × Ω => Real.exp (-α * p.1) * g (X p.1.toNNReal p.2))
      ((volume.restrict (Ioi (0 : ℝ))).prod μ) := by
  obtain ⟨M, _, hb⟩ := h.observation_bound hg
  apply (((exp_neg_integrableOn_Ioi 0 hα).mul_const M).comp_fst μ).mono'
    (h.discounted_observation_measurable hg α).aestronglyMeasurable
  apply Eventually.of_forall
  intro p
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left (hb p.1.toNNReal p.2) (Real.exp_pos _).le

theorem ReversibleNeumannMartingaleProblem.discounted_observation_integral_integrable [IsProbabilityMeasure μ]
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) {α : ℝ} (hα : 0 < α) :
    Integrable (fun ω => ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * g (X t.toNNReal ω)) μ :=
  (h.discounted_observation_joint_integrable hg hα).integral_prod_right

theorem ReversibleNeumannMartingaleProblem.discounted_observation_swap [IsProbabilityMeasure μ]
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) {α : ℝ} (hα : 0 < α) :
    (∫ ω, (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * g (X t.toNNReal ω)) ∂μ) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * ∫ ω, g (X t.toNNReal ω) ∂μ := by
  exact (integral_integral_swap (h.discounted_observation_joint_integrable hg hα)).symm.trans
    (integral_congr_ae (Eventually.of_forall (fun t => integral_const_mul _ _)))

end TimeTraps.Probability

end
