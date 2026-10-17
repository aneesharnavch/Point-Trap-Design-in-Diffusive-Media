module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemLaplace
public import TimeTraps.Probability.BoundedContinuousLaplaceUniqueness

@[expose] public section

/-! Every one-time law of an arbitrary continuous-version solution of
the original Neumann martingale problem is uniquely determined. Neither
competitor is assumed Markov. The actual resistance-clock process supplies
a witness, and its literal transition expectation is recovered. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal BoundedContinuousFunction

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {A : IntervalMedium} {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
variable {G : Filtration ℝ≥0 mΩ} {F : Filtration ℝ≥0 mΩ'}
variable {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.continuous_observation_eq
    (hX : ReversibleNeumannMartingaleProblem A X G μ x)
    (hY : ReversibleNeumannMartingaleProblem A Y F ν x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (t : ℝ≥0) :
    (∫ ω, g (X t ω) ∂μ) = ∫ ω, g (Y t ω) ∂ν := by
  obtain ⟨M, _, hM⟩ := hX.observation_mean_bound hg
  obtain ⟨N, _, hN⟩ := hY.observation_mean_bound hg
  have he := boundedContinuous_nonnegativeTime_laplace_unique
    (hX.observation_mean_continuous hg) (hY.observation_mean_continuous hg) hM hN
      (fun _ hα => hX.continuous_observation_laplace_eq hY hg hα)
  exact congrFun he t

theorem ReversibleNeumannMartingaleProblem.one_time_law_eq
    (hX : ReversibleNeumannMartingaleProblem A X G μ x)
    (hY : ReversibleNeumannMartingaleProblem A Y F ν x) (t : ℝ≥0) :
    μ.map (X t) = ν.map (Y t) := by
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  rw [integral_map ((hX.adapted t).mono (G.le t)).measurable.aemeasurable
      f.continuous.aestronglyMeasurable,
    integral_map ((hY.adapted t).mono (F.le t)).measurable.aemeasurable
      f.continuous.aestronglyMeasurable]
  exact hX.continuous_observation_eq hY f.continuous.continuousOn t

theorem ReversibleNeumannMartingaleProblem.one_time_law_reference
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    (hx : x ∈ Icc A.source.left A.source.right) (t : ℝ≥0) :
    μ.map (X t) = brownianCompletedMeasure.map (fun ω : BrownianCompletedSample => reversibleResistancePath A x t ω) :=
  h.one_time_law_eq (Ω' := BrownianCompletedSample)
    (Y := fun t (ω : BrownianCompletedSample) => reversibleResistancePath A x t ω)
    (reversibleResistancePath_martingaleProblem A hx) t

theorem ReversibleNeumannMartingaleProblem.continuous_observation_transition
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    (hx : x ∈ Icc A.source.left A.source.right)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) (t : ℝ≥0) :
    (∫ ω, g (X t ω) ∂μ) = reversibleResistanceTransition A t g x :=
  h.continuous_observation_eq (Ω' := BrownianCompletedSample)
    (Y := fun t (ω : BrownianCompletedSample) => reversibleResistancePath A x t ω)
    (reversibleResistancePath_martingaleProblem A hx) hg t

end TimeTraps.Probability

end
