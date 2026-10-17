module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemRestart

@[expose] public section

/-! Resolvent-test martingales determine event-weighted future Laplace
transforms after each deterministic time. The initial value is retained
as the actual random present state inside the same event integral. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium}
variable {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.restart_test_laplace
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ReversibleNeumannTest A)
    (s : ℝ≥0) {E : Set Ω} (hE : MeasurableSet[G s] E) {α : ℝ} (hα : 0 < α) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
      ∫ ω in E, α * H.value (X (s + t.toNNReal) ω) - H.generator (X (s + t.toNNReal) ω) ∂μ) =
      ∫ ω in E, H.value (X s ω) ∂μ := by
  let u : ℝ → ℝ := fun t => ∫ ω in E, H.value (X (s + t.toNNReal) ω) ∂μ
  let v : ℝ → ℝ := fun t => ∫ ω in E, H.generator (X (s + t.toNNReal) ω) ∂μ
  have hu : Continuous u :=
    (h.restart_observation_mean_continuous H.value_continuous E s).comp continuous_real_toNNReal
  have hv : Continuous v :=
    (h.restart_observation_mean_continuous H.generator_continuous E s).comp continuous_real_toNNReal
  obtain ⟨M, hM⟩ := h.restart_observation_mean_bound H.value_continuous E s
  obtain ⟨N, hN⟩ := h.restart_observation_mean_bound H.generator_continuous E s
  have hu0 : u 0 = ∫ ω in E, H.value (X s ω) ∂μ := by
    simp only [u, Real.toNNReal_zero, add_zero]
  have hdyn : ∀ T, 0 ≤ T → u T = u 0 + ∫ r in (0 : ℝ)..T, v r := by
    intro T hT
    exact (h.restart_expected_dynkin_real H s hT hE).trans
      (congrArg (fun z : ℝ => z + ∫ r in (0 : ℝ)..T, v r) hu0.symm)
  have hlap := boundedDynkin_laplace_identity hu hv
    (fun t => hM t.toNNReal) (fun t => hN t.toNNReal) hdyn hα
  have hlin (t : ℝ) :
      (∫ ω in E, α * H.value (X (s + t.toNNReal) ω) - H.generator (X (s + t.toNNReal) ω) ∂μ) =
        α * u t - v t :=
    (integral_sub (((h.observation_integrable H.value_continuous (s + t.toNNReal)).restrict).const_mul α)
      ((h.observation_integrable H.generator_continuous (s + t.toNNReal)).restrict)).trans
        (congrArg (fun z : ℝ => z - v t) (integral_const_mul α _))
  exact (integral_congr_ae (Eventually.of_forall (fun t =>
    congrArg (fun z : ℝ => Real.exp (-α * t) * z) (hlin t)))).trans (hlap.trans hu0)

theorem ReversibleNeumannMartingaleProblem.restart_resolvent_laplace
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ReversibleNeumannTest A)
    (s : ℝ≥0) {E : Set Ω} (hE : MeasurableSet[G s] E) {α : ℝ} (hα : 0 < α)
    {g : ℝ → ℝ}
    (hres : ∀ y ∈ Icc A.source.left A.source.right, α * H.value y - H.generator y = g y) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * ∫ ω in E, g (X (s + t.toNNReal) ω) ∂μ) =
      ∫ ω in E, H.value (X s ω) ∂μ := by
  have he (t : ℝ) : (∫ ω in E, g (X (s + t.toNNReal) ω) ∂μ) =
      ∫ ω in E, α * H.value (X (s + t.toNNReal) ω) - H.generator (X (s + t.toNNReal) ω) ∂μ :=
    integral_congr_ae (Eventually.of_forall (fun ω => (hres _ (h.path_mem (s + t.toNNReal) ω)).symm))
  exact (integral_congr_ae (Eventually.of_forall (fun t =>
    congrArg (fun z : ℝ => Real.exp (-α * t) * z) (he t)))).trans
      (h.restart_test_laplace H s hE hα)

end TimeTraps.Probability

end
