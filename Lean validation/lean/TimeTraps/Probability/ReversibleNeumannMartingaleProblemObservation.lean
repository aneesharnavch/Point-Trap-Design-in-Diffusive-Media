module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemData
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! Continuous spatial observations of an arbitrary competing process
have the measurability, boundedness, integrability and continuous expected
values needed for law identification. These facts use compact physical
range and continuous paths, without any transition or Markov premise. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium}
variable {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.observation_continuous
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (ω : Ω) :
    Continuous (fun t => g (X t ω)) :=
  hg.comp_continuous (h.path_continuous ω) (fun t => h.path_mem t ω)

theorem ReversibleNeumannMartingaleProblem.observation_bound
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ω, ‖g (X t ω)‖ ≤ M := by
  let f : C(Icc A.source.left A.source.right, ℝ) := ⟨fun y => g y.val, hg.domRestrict⟩
  exact ⟨‖f‖, norm_nonneg f, fun t ω => f.norm_coe_le_norm ⟨X t ω, h.path_mem t ω⟩⟩

theorem ReversibleNeumannMartingaleProblem.observation_stronglyMeasurable
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (t : ℝ≥0) :
    StronglyMeasurable[G t] (fun ω => g (X t ω)) := by
  let f : C(Icc A.source.left A.source.right, ℝ) := ⟨fun y => g y.val, hg.domRestrict⟩
  have hm : Measurable[G t] (fun ω => (⟨X t ω, h.path_mem t ω⟩ : Icc A.source.left A.source.right)) :=
    (h.adapted t).measurable.subtype_mk
  exact (f.continuous.measurable.comp hm).stronglyMeasurable

theorem ReversibleNeumannMartingaleProblem.observation_jointlyMeasurable
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) :
    Measurable (fun p : ℝ≥0 × Ω => g (X p.1 p.2)) :=
  measurable_uncurry_of_continuous_of_measurable (h.observation_continuous hg)
    (fun t => ((h.observation_stronglyMeasurable hg t).mono (G.le t)).measurable)

theorem ReversibleNeumannMartingaleProblem.observation_integrable [IsProbabilityMeasure μ]
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (t : ℝ≥0) :
    Integrable (fun ω => g (X t ω)) μ := by
  obtain ⟨M, _, hb⟩ := h.observation_bound hg
  exact (integrable_const M).mono'
    (((h.observation_stronglyMeasurable hg t).mono (G.le t)).aestronglyMeasurable)
      (Eventually.of_forall (hb t))

theorem ReversibleNeumannMartingaleProblem.observation_mean_continuous [IsProbabilityMeasure μ]
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) :
    Continuous (fun t : ℝ≥0 => ∫ ω, g (X t ω) ∂μ) := by
  obtain ⟨M, _, hb⟩ := h.observation_bound hg
  exact continuous_of_dominated (fun t => (h.observation_integrable hg t).aestronglyMeasurable)
    (fun t => Eventually.of_forall (hb t)) (integrable_const M)
      (Eventually.of_forall (h.observation_continuous hg))

theorem ReversibleNeumannMartingaleProblem.observation_timeProduct_integrable [IsProbabilityMeasure μ]
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (T : ℝ≥0) :
    Integrable (fun p : ℝ × Ω => g (X p.1.toNNReal p.2))
      ((volume.restrict (uIoc (0 : ℝ) T.val)).prod μ) := by
  let : IsFiniteMeasure (volume.restrict (uIoc (0 : ℝ) T.val)) :=
    isFiniteMeasure_restrict.mpr (by rw [uIoc_of_le T.property]; exact measure_Ioc_lt_top.ne)
  obtain ⟨M, _, hb⟩ := h.observation_bound hg
  have hm : Measurable (fun p : ℝ × Ω => g (X p.1.toNNReal p.2)) :=
    (h.observation_jointlyMeasurable hg).comp
      ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd)
  exact (integrable_const M).mono' hm.aestronglyMeasurable
    (Eventually.of_forall (fun p => hb p.1.toNNReal p.2))

end TimeTraps.Probability

end
