module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemTransitionData
public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemRestartLaplace

@[expose] public section

/-! The deterministic-time Markov identity is derived for arbitrary
continuous-version solutions of the original martingale problem. Every
bounded continuous spatial test uses the actual resistance transition.
The proof compares event-weighted Laplace transforms and uses the proved
injectivity theorem; no competitor Markov premise is present. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology BoundedContinuousFunction

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium}
variable {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.transition_resolvent_laplace
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ReversibleNeumannTest A)
    (f : ℝ →ᵇ ℝ) (s : ℝ≥0) (E : Set Ω) {α : ℝ} (hα : 0 < α)
    (hres : ∀ y ∈ Icc A.source.left A.source.right, α * H.value y - H.generator y = f y) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
      ∫ ω in E, reversibleResistanceTransition A t.toNNReal f (X s ω) ∂μ) =
        ∫ ω in E, H.value (X s ω) ∂μ := by
  apply (h.transition_discounted_swap f s E hα).symm.trans
  apply integral_congr_ae
  apply Eventually.of_forall
  intro ω
  exact ReversibleNeumannMartingaleProblem.resolvent_laplace (Ω := BrownianCompletedSample)
    (X := fun t (η : BrownianCompletedSample) => reversibleResistancePath A (X s ω) t η)
    (reversibleResistancePath_martingaleProblem A (h.path_mem s ω)) H hα hres

theorem ReversibleNeumannMartingaleProblem.markov_setIntegral
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (f : ℝ →ᵇ ℝ) (s t : ℝ≥0)
    {E : Set Ω} (hE : MeasurableSet[G s] E) :
    (∫ ω in E, f (X (s + t) ω) ∂μ) =
      ∫ ω in E, reversibleResistanceTransition A t f (X s ω) ∂μ := by
  obtain ⟨M, hM⟩ := h.restart_observation_mean_bound f.continuous.continuousOn E s
  obtain ⟨N, hN⟩ := h.transition_mean_bound f s E
  have he := boundedContinuous_nonnegativeTime_laplace_unique
    (h.restart_observation_mean_continuous f.continuous.continuousOn E s)
    (h.transition_mean_continuous f s E) hM hN (fun α hα => ?_)
  · exact congrFun he t
  · obtain ⟨H, hH⟩ := reversibleNeumann_resolvent_test_exists A f.continuous.continuousOn hα
    exact (h.restart_resolvent_laplace H s hE hα hH).trans
      (h.transition_resolvent_laplace H f s E hα hH).symm

theorem ReversibleNeumannMartingaleProblem.markov
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (f : ℝ →ᵇ ℝ) (s t : ℝ≥0) :
    μ[(fun ω => f (X (s + t) ω)) | G s] =ᵐ[μ]
      (fun ω => reversibleResistanceTransition A t f (X s ω)) := by
  let z : Ω → Icc A.source.left A.source.right := fun ω => ⟨X s ω, h.path_mem s ω⟩
  have hz : Measurable[G s] z := (h.adapted s).measurable.subtype_mk
  have hsm : StronglyMeasurable[G s] (fun ω => reversibleResistanceTransition A t f (X s ω)) :=
    ((reversibleResistanceTransition_measurable_interval A t f.continuous.measurable).comp hz).stronglyMeasurable
  have hi : Integrable (fun ω => reversibleResistanceTransition A t f (X s ω)) μ := by
    apply (integrable_const ‖f‖).mono' (hsm.mono (G.le s)).aestronglyMeasurable
    exact Eventually.of_forall (fun ω =>
      reversibleResistanceTransition_bound A t (fun y => f.norm_coe_le_norm y) (X s ω))
  apply (ae_eq_condExp_of_forall_setIntegral_eq (G.le s)
    (h.observation_integrable f.continuous.continuousOn (s + t)) _ _ hsm.aestronglyMeasurable).symm
  · exact fun _ _ _ => hi.integrableOn
  · exact fun _ hE _ => (h.markov_setIntegral f s t hE).symm

end TimeTraps.Probability

end
