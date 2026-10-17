module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemOneTime

@[expose] public section

/-! Event-weighted observations after a deterministic restart retain
continuous means and derived finite-time integrability. The clock shift is
an actual interval-integral substitution, not a Markov assumption. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem nonnegativeTime_integral_shift {f : ℝ≥0 → ℝ} (hf : Continuous f) (s t : ℝ≥0) :
    (∫ r in (0 : ℝ)..(s + t).val, f r.toNNReal) =
      (∫ r in (0 : ℝ)..s.val, f r.toNNReal) +
        ∫ r in (0 : ℝ)..t.val, f (s + r.toNNReal) := by
  have hc : Continuous (fun r : ℝ => f r.toNNReal) := hf.comp continuous_real_toNNReal
  have he := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable 0 s.val) (hc.intervalIntegrable s.val (s.val + t.val))
  have hs : (∫ r in (0 : ℝ)..t.val, f (s + r.toNNReal)) =
      ∫ r in s.val..s.val + t.val, f r.toNNReal := by
    calc
      _ = ∫ r in (0 : ℝ)..t.val, f ((s : ℝ) + r).toNNReal := by
        apply intervalIntegral.integral_congr
        intro r hr
        have hr0 : 0 ≤ r := (uIcc_of_le t.property ▸ hr).1
        change f (s + r.toNNReal) = f ((s : ℝ) + r).toNNReal
        apply congrArg f
        apply NNReal.coe_injective
        change (s : ℝ) + (r.toNNReal : ℝ) = (((s : ℝ) + r).toNNReal : ℝ)
        exact (congrArg (fun z : ℝ => (s : ℝ) + z) (Real.coe_toNNReal r hr0)).trans
          (Real.coe_toNNReal ((s : ℝ) + r) (add_nonneg s.property hr0)).symm
      _ = _ := by
        convert! intervalIntegral.integral_comp_add_left
          (fun r : ℝ => f r.toNNReal) (a := 0) (b := t.val) s.val using 1
        simp only [add_zero]
  exact he.symm.trans (congrArg (fun z : ℝ => (∫ r in (0 : ℝ)..s.val, f r.toNNReal) + z) hs.symm)

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium}
variable {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.restart_observation_mean_continuous
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (E : Set Ω) (s : ℝ≥0) :
    Continuous (fun t : ℝ≥0 => ∫ ω in E, g (X (s + t) ω) ∂μ) := by
  obtain ⟨M, _, hb⟩ := h.observation_bound hg
  apply continuous_of_dominated
    (fun t => (h.observation_integrable hg (s + t)).restrict.aestronglyMeasurable)
    (fun t => Eventually.of_forall (hb (s + t))) (integrable_const M)
  exact Eventually.of_forall (fun ω => (h.observation_continuous hg ω).comp (continuous_const.add continuous_id))

theorem ReversibleNeumannMartingaleProblem.restart_observation_mean_bound
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (E : Set Ω) (s : ℝ≥0) :
    ∃ M : ℝ, ∀ t : ℝ≥0, ‖∫ ω in E, g (X (s + t) ω) ∂μ‖ ≤ M := by
  obtain ⟨M, _, hb⟩ := h.observation_bound hg
  exact ⟨M * (μ.restrict E).real univ, fun t =>
    norm_integral_le_of_norm_le_const (Eventually.of_forall (hb (s + t)))⟩

theorem ReversibleNeumannMartingaleProblem.restart_observation_timeProduct_integrable
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right))
    (E : Set Ω) (s T : ℝ≥0) :
    Integrable (fun p : ℝ × Ω => g (X (s + p.1.toNNReal) p.2))
      ((volume.restrict (uIoc (0 : ℝ) T.val)).prod (μ.restrict E)) := by
  let : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) T.val)) :=
    isFiniteMeasure_restrict.mpr (by rw [uIoc_of_le T.property]; exact measure_Ioc_lt_top.ne)
  obtain ⟨M, _, hb⟩ := h.observation_bound hg
  have hm : Measurable (fun p : ℝ × Ω => g (X (s + p.1.toNNReal) p.2)) :=
    (h.observation_jointlyMeasurable hg).comp
      ((by fun_prop : Measurable (fun p : ℝ × Ω => s + p.1.toNNReal)).prodMk measurable_snd)
  exact (integrable_const M).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun p => hb (s + p.1.toNNReal) p.2))

theorem ReversibleNeumannMartingaleProblem.restart_observation_timeIntegral_integrable
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right))
    (E : Set Ω) (s T : ℝ≥0) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..T.val, g (X (s + r.toNNReal) ω)) (μ.restrict E) := by
  have hi := (h.restart_observation_timeProduct_integrable hg E s T).integral_prod_right
  simpa only [intervalIntegral.integral_of_le T.property, uIoc_of_le T.property] using hi

theorem ReversibleNeumannMartingaleProblem.restart_observation_timeIntegral_mean
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right))
    (E : Set Ω) (s T : ℝ≥0) :
    (∫ ω in E, (∫ r in (0 : ℝ)..T.val, g (X (s + r.toNNReal) ω)) ∂μ) =
      ∫ r in (0 : ℝ)..T.val, ∫ ω in E, g (X (s + r.toNNReal) ω) ∂μ :=
  (intervalIntegral_integral_swap (h.restart_observation_timeProduct_integrable hg E s T)).symm

end TimeTraps.Probability

end
