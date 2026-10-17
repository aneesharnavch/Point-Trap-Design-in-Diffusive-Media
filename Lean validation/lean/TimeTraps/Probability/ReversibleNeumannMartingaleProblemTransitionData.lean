module

public import TimeTraps.Probability.ReversibleResistanceTransitionRegularity

@[expose] public section

/-! Actual transition expectations evaluated at a competitor's present
state have joint measurability, continuous event-weighted means, and
absolutely integrable discounted time products. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology BoundedContinuousFunction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium}
variable {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℝ}

omit [IsProbabilityMeasure μ] in
theorem ReversibleNeumannMartingaleProblem.transition_jointlyMeasurable
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (f : ℝ →ᵇ ℝ) (s : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × Ω => reversibleResistanceTransition A p.1 f (X s p.2)) := by
  let z : Ω → Icc A.source.left A.source.right := fun ω => ⟨X s ω, h.path_mem s ω⟩
  have hz : Measurable z := ((h.adapted s).mono (G.le s)).measurable.subtype_mk
  have hm := (reversibleResistanceTransition_jointlyMeasurable_interval A f.continuous).comp
    (measurable_fst.prodMk (hz.comp measurable_snd))
  have he : (fun p : ℝ≥0 × Ω => reversibleResistanceTransition A p.1 f (X s p.2)) =
      (fun p : ℝ≥0 × Icc A.source.left A.source.right =>
        reversibleResistanceTransition A p.1 f p.2.val) ∘ (fun p => (p.1, z p.2)) := rfl
  exact he.symm ▸ hm

theorem ReversibleNeumannMartingaleProblem.transition_mean_continuous
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (f : ℝ →ᵇ ℝ) (s : ℝ≥0) (E : Set Ω) :
    Continuous (fun t : ℝ≥0 => ∫ ω in E, reversibleResistanceTransition A t f (X s ω) ∂μ) := by
  apply continuous_of_dominated
    (fun t => ((h.transition_jointlyMeasurable f s).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable)
    (fun t => Eventually.of_forall (fun ω =>
      reversibleResistanceTransition_bound A t (fun y => f.norm_coe_le_norm y) (X s ω)))
    (integrable_const ‖f‖)
  exact Eventually.of_forall (fun ω =>
    reversibleResistanceTransition_continuous_time A (h.path_mem s ω) f.continuous.continuousOn)

theorem ReversibleNeumannMartingaleProblem.transition_mean_bound
    (_h : ReversibleNeumannMartingaleProblem A X G μ x) (f : ℝ →ᵇ ℝ) (s : ℝ≥0) (E : Set Ω) :
    ∃ M : ℝ, ∀ t : ℝ≥0,
      ‖∫ ω in E, reversibleResistanceTransition A t f (X s ω) ∂μ‖ ≤ M := by
  refine ⟨‖f‖ * (μ.restrict E).real univ, fun t => ?_⟩
  exact norm_integral_le_of_norm_le_const (Eventually.of_forall (fun ω =>
    reversibleResistanceTransition_bound A t (fun y => f.norm_coe_le_norm y) (X s ω)))

theorem ReversibleNeumannMartingaleProblem.transition_discounted_joint_integrable
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (f : ℝ →ᵇ ℝ) (s : ℝ≥0) (E : Set Ω)
    {α : ℝ} (hα : 0 < α) :
    Integrable (fun p : ℝ × Ω => Real.exp (-α * p.1) *
      reversibleResistanceTransition A p.1.toNNReal f (X s p.2))
        ((volume.restrict (Ioi (0 : ℝ))).prod (μ.restrict E)) := by
  have hm0 := (h.transition_jointlyMeasurable f s).comp
    ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd)
  have he : (fun p : ℝ × Ω => reversibleResistanceTransition A p.1.toNNReal f (X s p.2)) =
      (fun p : ℝ≥0 × Ω => reversibleResistanceTransition A p.1 f (X s p.2)) ∘
        (fun p : ℝ × Ω => (p.1.toNNReal, p.2)) := rfl
  have hm : Measurable (fun p : ℝ × Ω => reversibleResistanceTransition A p.1.toNNReal f (X s p.2)) :=
    he.symm ▸ hm0
  apply (((exp_neg_integrableOn_Ioi 0 hα).mul_const ‖f‖).comp_fst (μ.restrict E)).mono'
    (((by fun_prop : Measurable (fun p : ℝ × Ω => Real.exp (-α * p.1))).mul hm).aestronglyMeasurable)
  apply Eventually.of_forall
  intro p
  change ‖Real.exp (-α * p.1) * reversibleResistanceTransition A p.1.toNNReal f (X s p.2)‖ ≤
    Real.exp (-α * p.1) * ‖f‖
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul_of_nonneg_left
    (reversibleResistanceTransition_bound A p.1.toNNReal (fun y => f.norm_coe_le_norm y) (X s p.2))
    (Real.exp_pos _).le

theorem ReversibleNeumannMartingaleProblem.transition_discounted_swap
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (f : ℝ →ᵇ ℝ) (s : ℝ≥0) (E : Set Ω)
    {α : ℝ} (hα : 0 < α) :
    (∫ ω in E, (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
      reversibleResistanceTransition A t.toNNReal f (X s ω)) ∂μ) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
        ∫ ω in E, reversibleResistanceTransition A t.toNNReal f (X s ω) ∂μ :=
  (integral_integral_swap (h.transition_discounted_joint_integrable f s E hα)).symm.trans
    (integral_congr_ae (Eventually.of_forall (fun _t => integral_const_mul _ _)))

end TimeTraps.Probability

end
