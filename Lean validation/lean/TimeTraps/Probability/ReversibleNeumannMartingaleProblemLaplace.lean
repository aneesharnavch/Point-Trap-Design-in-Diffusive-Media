module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemLaplaceData
public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemDiscounted

@[expose] public section

/-! The original Neumann martingale problem determines every positive
Laplace transform of every continuous one-time observation. Resolvent
test existence is derived earlier for the original coefficients. Competing
processes may have different probability spaces and filtrations, and no
Markov property or transition identity is required of either process. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium}
variable {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.observation_mean_bound
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t : ℝ≥0, ‖∫ ω, g (X t ω) ∂μ‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := h.observation_bound hg
  refine ⟨M, hM, fun t => ?_⟩
  simpa only [probReal_univ, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := μ) (f := fun ω => g (X t ω))
      (C := M) (Eventually.of_forall (hb t)))

theorem ReversibleNeumannMartingaleProblem.initial_observation_mean
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (g : ℝ → ℝ) :
    (∫ ω, g (X 0 ω) ∂μ) = g x := by
  calc
    _ = ∫ _ω : Ω, g x ∂μ := integral_congr_ae (h.initial.mono (fun _ he => congrArg g he))
    _ = _ := by simp

theorem ReversibleNeumannMartingaleProblem.test_laplace
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    (H : ReversibleNeumannTest A) {α : ℝ} (hα : 0 < α) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
      ∫ ω, α * H.value (X t.toNNReal ω) - H.generator (X t.toNNReal ω) ∂μ) = H.value x := by
  let u : ℝ → ℝ := fun t => ∫ ω, H.value (X t.toNNReal ω) ∂μ
  let v : ℝ → ℝ := fun t => ∫ ω, H.generator (X t.toNNReal ω) ∂μ
  have hu : Continuous u :=
    (h.observation_mean_continuous H.value_continuous).comp continuous_real_toNNReal
  have hv : Continuous v :=
    (h.observation_mean_continuous H.generator_continuous).comp continuous_real_toNNReal
  obtain ⟨M, _, hM⟩ := h.observation_mean_bound H.value_continuous
  obtain ⟨N, _, hN⟩ := h.observation_mean_bound H.generator_continuous
  have hu0 : u 0 = H.value x := by
    simpa only [u, Real.toNNReal_zero] using h.initial_observation_mean H.value
  have hdyn : ∀ T, 0 ≤ T → u T = u 0 + ∫ r in (0 : ℝ)..T, v r := by
    intro T hT
    exact (h.expected_dynkin_real H hT).trans
      (congrArg (fun z : ℝ => z + ∫ r in (0 : ℝ)..T, v r) hu0.symm)
  have hlap := boundedDynkin_laplace_identity hu hv
    (fun t => hM t.toNNReal) (fun t => hN t.toNNReal) hdyn hα
  have hlin (t : ℝ) :
      (∫ ω, α * H.value (X t.toNNReal ω) - H.generator (X t.toNNReal ω) ∂μ) = α * u t - v t :=
    (integral_sub ((h.observation_integrable H.value_continuous t.toNNReal).const_mul α)
      (h.observation_integrable H.generator_continuous t.toNNReal)).trans
        (congrArg (fun z : ℝ => z - v t) (integral_const_mul α _))
  exact (integral_congr_ae (Eventually.of_forall (fun t =>
    congrArg (fun z : ℝ => Real.exp (-α * t) * z) (hlin t)))).trans (hlap.trans hu0)

theorem ReversibleNeumannMartingaleProblem.resolvent_laplace
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    (H : ReversibleNeumannTest A) {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ}
    (hres : ∀ y ∈ Icc A.source.left A.source.right, α * H.value y - H.generator y = g y) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * ∫ ω, g (X t.toNNReal ω) ∂μ) = H.value x := by
  have he (t : ℝ) : (∫ ω, g (X t.toNNReal ω) ∂μ) =
      ∫ ω, α * H.value (X t.toNNReal ω) - H.generator (X t.toNNReal ω) ∂μ :=
    integral_congr_ae (Eventually.of_forall (fun ω => (hres _ (h.path_mem t.toNNReal ω)).symm))
  exact (integral_congr_ae (Eventually.of_forall (fun t =>
    congrArg (fun z : ℝ => Real.exp (-α * t) * z) (he t)))).trans (h.test_laplace H hα)

theorem ReversibleNeumannMartingaleProblem.resolvent_expected_integral
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    (H : ReversibleNeumannTest A) {α : ℝ} (hα : 0 < α) {g : ℝ → ℝ}
    (hg : ContinuousOn g (Icc A.source.left A.source.right))
    (hres : ∀ y ∈ Icc A.source.left A.source.right, α * H.value y - H.generator y = g y) :
    (∫ ω, (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * g (X t.toNNReal ω)) ∂μ) = H.value x :=
  (h.discounted_observation_swap hg hα).trans (h.resolvent_laplace H hα hres)

theorem ReversibleNeumannMartingaleProblem.continuous_observation_laplace_eq
    {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {Y : ℝ≥0 → Ω' → ℝ}
    {F : Filtration ℝ≥0 mΩ'} {ν : Measure Ω'} [IsProbabilityMeasure ν]
    (hX : ReversibleNeumannMartingaleProblem A X G μ x)
    (hY : ReversibleNeumannMartingaleProblem A Y F ν x)
    {g : ℝ → ℝ} (hg : ContinuousOn g (Icc A.source.left A.source.right)) {α : ℝ} (hα : 0 < α) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * ∫ ω, g (X t.toNNReal ω) ∂μ) =
      ∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * ∫ ω, g (Y t.toNNReal ω) ∂ν := by
  obtain ⟨H, hH⟩ := reversibleNeumann_resolvent_test_exists A hg hα
  exact (hX.resolvent_laplace H hα hH).trans (hY.resolvent_laplace H hα hH).symm

end TimeTraps.Probability

end
