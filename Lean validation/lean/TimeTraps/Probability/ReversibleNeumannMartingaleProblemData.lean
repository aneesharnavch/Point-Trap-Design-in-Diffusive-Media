module

public import TimeTraps.Probability.ReversibleResistanceNeumannDomainMartingale
public import TimeTraps.Probability.ReflectedBoundedStrongMarkovResistance
public import TimeTraps.Probability.ReversibleResistanceNeumannResolvent

@[expose] public section

/-! A competing continuous-version process is specified only by its
physical range, adaptation, initial law and all original Neumann test
martingales. No Markov, strong Markov, transition law or uniqueness
condition is part of the definition. The constructed resistance process
is proved to satisfy this same definition. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

def reversibleNeumannTestProcess {A : IntervalMedium} (H : ReversibleNeumannTest A)
    (X : ℝ≥0 → Ω → ℝ) (x : ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  H.value (X t ω) - H.value x - ∫ r in (0 : ℝ)..t.val, H.generator (X r.toNNReal ω)

structure ReversibleNeumannMartingaleProblem (A : IntervalMedium)
    (X : ℝ≥0 → Ω → ℝ) (G : Filtration ℝ≥0 mΩ) (μ : Measure Ω) (x : ℝ) : Prop where
  path_mem : ∀ t ω, X t ω ∈ Icc A.source.left A.source.right
  path_continuous : ∀ ω, Continuous (fun t => X t ω)
  adapted : StronglyAdapted G X
  initial : ∀ᵐ ω ∂μ, X 0 ω = x
  test_martingale : ∀ H : ReversibleNeumannTest A,
    Martingale (reversibleNeumannTestProcess H X x) G μ

theorem reversibleResistancePath_martingaleProblem (A : IntervalMedium) {x : ℝ}
    (hx : x ∈ Icc A.source.left A.source.right) :
    ReversibleNeumannMartingaleProblem A (fun t ω => reversibleResistancePath A x t ω)
      (reversibleResistanceFiltration A x) brownianCompletedMeasure x := by
  refine ⟨reversibleResistancePath_mem A x, reversibleResistancePath_continuous A x,
    fun t => reversibleResistancePath_borel_stronglyMeasurable A x t measurable_id,
      reversibleResistancePath_initial_ae A hx, fun H => ?_⟩
  exact reversibleNeumannDynkin_martingale H hx

theorem ReversibleNeumannMartingaleProblem.test_zero_ae {A : IntervalMedium}
    {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} {x : ℝ}
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ReversibleNeumannTest A) :
    reversibleNeumannTestProcess H X x 0 =ᵐ[μ] (fun _ => 0) := by
  filter_upwards [h.initial] with ω hω
  change H.value (X 0 ω) - H.value x - ∫ r in (0 : ℝ)..0, H.generator (X r.toNNReal ω) = 0
  rw [hω, intervalIntegral.integral_same, sub_self, sub_zero]

theorem ReversibleNeumannMartingaleProblem.test_mean {A : IntervalMedium}
    {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℝ}
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ReversibleNeumannTest A) (t : ℝ≥0) :
    (∫ ω, reversibleNeumannTestProcess H X x t ω ∂μ) = 0 := by
  have he := (h.test_martingale H).setIntegral_eq (show (0 : ℝ≥0) ≤ t from bot_le)
    (s := univ) MeasurableSet.univ
  simp only [Measure.restrict_univ] at he
  exact he.symm.trans ((integral_congr_ae (h.test_zero_ae H)).trans (integral_zero _ _))

end TimeTraps.Probability

end
