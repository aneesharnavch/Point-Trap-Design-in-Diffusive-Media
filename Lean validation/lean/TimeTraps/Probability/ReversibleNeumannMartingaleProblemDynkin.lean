module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemObservation

@[expose] public section

/-! Expected Dynkin identity for every competing continuous process.
Compactness supplies full time/sample integrability, so Fubini and the
zero-mean test martingales yield the original generator identity without
an assumed Markov law or an extra integrability hypothesis. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium}
variable {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.observation_timeIntegral_integrable
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (T : ℝ≥0) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..T.val, g (X r.toNNReal ω)) μ := by
  have hi := (h.observation_timeProduct_integrable hg T).integral_prod_right
  simpa only [intervalIntegral.integral_of_le T.property, uIoc_of_le T.property] using hi

theorem ReversibleNeumannMartingaleProblem.observation_timeIntegral_mean
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val, g (X r.toNNReal ω)) ∂μ) =
      ∫ r in (0 : ℝ)..T.val, ∫ ω, g (X r.toNNReal ω) ∂μ :=
  (intervalIntegral_integral_swap (h.observation_timeProduct_integrable hg T)).symm

theorem ReversibleNeumannMartingaleProblem.expected_dynkin
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ReversibleNeumannTest A) (T : ℝ≥0) :
    (∫ ω, H.value (X T ω) ∂μ) =
      H.value x + ∫ r in (0 : ℝ)..T.val, ∫ ω, H.generator (X r.toNNReal ω) ∂μ := by
  have hi := h.observation_integrable H.value_continuous T
  have ht := h.observation_timeIntegral_integrable H.generator_continuous T
  have he := h.test_mean H T
  change (∫ ω, H.value (X T ω) - H.value x -
    (∫ r in (0 : ℝ)..T.val, H.generator (X r.toNNReal ω)) ∂μ) = 0 at he
  have hc : (∫ _ω : Ω, H.value x ∂μ) = H.value x := by simp
  have hv : (∫ ω, H.value (X T ω) - H.value x ∂μ) =
      (∫ ω, H.value (X T ω) ∂μ) - H.value x :=
    (integral_sub hi (integrable_const (H.value x))).trans
      (congrArg (fun z : ℝ => (∫ ω, H.value (X T ω) ∂μ) - z) hc)
  have hexp : (∫ ω, H.value (X T ω) - H.value x -
      (∫ r in (0 : ℝ)..T.val, H.generator (X r.toNNReal ω)) ∂μ) =
      (∫ ω, H.value (X T ω) ∂μ) - H.value x -
        (∫ ω, (∫ r in (0 : ℝ)..T.val, H.generator (X r.toNNReal ω)) ∂μ) :=
    (integral_sub (hi.sub (integrable_const (H.value x))) ht).trans
      (congrArg (fun z : ℝ => z -
        (∫ ω, (∫ r in (0 : ℝ)..T.val, H.generator (X r.toNNReal ω)) ∂μ)) hv)
  have hz := hexp.symm.trans he
  have htmean := h.observation_timeIntegral_mean H.generator_continuous T
  linarith

theorem ReversibleNeumannMartingaleProblem.expected_dynkin_real
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ReversibleNeumannTest A)
    {T : ℝ} (hT : 0 ≤ T) :
    (∫ ω, H.value (X T.toNNReal ω) ∂μ) =
      H.value x + ∫ r in (0 : ℝ)..T, ∫ ω, H.generator (X r.toNNReal ω) ∂μ := by
  have he := h.expected_dynkin H T.toNNReal
  exact he.trans (congrArg (fun r : ℝ => H.value x +
    ∫ s in (0 : ℝ)..r, ∫ ω, H.generator (X s.toNNReal ω) ∂μ) (Real.coe_toNNReal T hT))

end TimeTraps.Probability

end
