module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemFiniteLaw

@[expose] public section

/-! Uniqueness in law on the full product measurable path space follows
from all finite-dimensional laws. Competitors may use different sample
spaces and filtrations. The independently constructed resistance process
is the identified law; no competitor Markov assumption is required. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {Ω Ω' : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'}
variable {A : IntervalMedium} {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
variable {G : Filtration ℝ≥0 mΩ} {F : Filtration ℝ≥0 mΩ'}
variable {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {x : ℝ}

omit [IsProbabilityMeasure μ] in
theorem ReversibleNeumannMartingaleProblem.process_measurable
    (h : ReversibleNeumannMartingaleProblem A X G μ x) :
    Measurable (fun ω => (fun t : ℝ≥0 => X t ω)) :=
  measurable_pi_lambda _ (fun t => ((h.adapted t).mono (G.le t)).measurable)

theorem ReversibleNeumannMartingaleProblem.process_law_eq
    (hX : ReversibleNeumannMartingaleProblem A X G μ x)
    (hY : ReversibleNeumannMartingaleProblem A Y F ν x) :
    μ.map (fun ω => (fun t : ℝ≥0 => X t ω)) = ν.map (fun ω => (fun t : ℝ≥0 => Y t ω)) := by
  have hpX := isProjectiveLimit_map (P := μ) hX.process_measurable.aemeasurable
  have hpY := isProjectiveLimit_map (P := ν) hY.process_measurable.aemeasurable
  have hlimit : IsProjectiveLimit (μ.map (fun ω => (fun t : ℝ≥0 => X t ω)))
      (fun S : Finset ℝ≥0 => ν.map (fun ω => S.restrict (fun t => Y t ω))) := by
    intro S
    exact (hpX S).trans (hX.finite_time_law_eq hY S)
  exact hlimit.unique hpY

theorem ReversibleNeumannMartingaleProblem.indexed_observation_law_eq
    {I : Type*} (hX : ReversibleNeumannMartingaleProblem A X G μ x)
    (hY : ReversibleNeumannMartingaleProblem A Y F ν x) (t : I → ℝ≥0) :
    μ.map (fun ω => (fun i => X (t i) ω)) = ν.map (fun ω => (fun i => Y (t i) ω)) := by
  have hm : Measurable (fun p : ℝ≥0 → ℝ => (fun i : I => p (t i))) :=
    measurable_pi_lambda _ (fun i => measurable_pi_apply (t i))
  have he := congrArg (Measure.map (fun p : ℝ≥0 → ℝ => (fun i : I => p (t i)))) (hX.process_law_eq hY)
  rw [Measure.map_map hm hX.process_measurable, Measure.map_map hm hY.process_measurable] at he
  exact he

theorem ReversibleNeumannMartingaleProblem.process_law_reference
    (h : ReversibleNeumannMartingaleProblem A X G μ x)
    (hx : x ∈ Icc A.source.left A.source.right) :
    μ.map (fun ω => (fun t : ℝ≥0 => X t ω)) =
      brownianCompletedMeasure.map (fun ω : BrownianCompletedSample =>
        (fun t : ℝ≥0 => reversibleResistancePath A x t ω)) :=
  h.process_law_eq (Ω' := BrownianCompletedSample)
    (Y := fun t (ω : BrownianCompletedSample) => reversibleResistancePath A x t ω)
    (reversibleResistancePath_martingaleProblem A hx)

end TimeTraps.Probability

end
