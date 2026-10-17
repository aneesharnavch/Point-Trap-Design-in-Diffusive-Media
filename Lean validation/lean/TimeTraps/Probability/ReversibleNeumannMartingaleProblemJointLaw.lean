module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemMarkov
public import TimeTraps.Probability.ContinuousObservationJointLaw

@[expose] public section

/-! Extending a common past law by one future observation preserves
law equality. The present state is a measurable function of that past.
The derived continuous-test Markov identity is sufficient, because finite
joint measures are determined on measurable past rectangles. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology BoundedContinuousFunction

theorem ReversibleNeumannMartingaleProblem.extend_past_law
    {Ω Ω' Z : Type*} {mΩ : MeasurableSpace Ω} {mΩ' : MeasurableSpace Ω'} [MeasurableSpace Z]
    {A : IntervalMedium} {X : ℝ≥0 → Ω → ℝ} {Y : ℝ≥0 → Ω' → ℝ}
    {G : Filtration ℝ≥0 mΩ} {F : Filtration ℝ≥0 mΩ'}
    {μ : Measure Ω} {ν : Measure Ω'} [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] {x : ℝ}
    (hX : ReversibleNeumannMartingaleProblem A X G μ x)
    (hY : ReversibleNeumannMartingaleProblem A Y F ν x)
    (s t : ℝ≥0) {P : Ω → Z} {Q : Ω' → Z}
    (hP : Measurable[G s] P) (hQ : Measurable[F s] Q)
    {p : Z → ℝ} (hp : Measurable p)
    (hPX : ∀ ω, p (P ω) = X s ω) (hQY : ∀ ω, p (Q ω) = Y s ω)
    (hpast : μ.map P = ν.map Q) :
    μ.map (fun ω => (P ω, X (s + t) ω)) = ν.map (fun ω => (Q ω, Y (s + t) ω)) := by
  have hPm : Measurable P := hP.mono (G.le s) le_rfl
  have hQm : Measurable Q := hQ.mono (F.le s) le_rfl
  apply jointLaw_eq_of_restricted_continuous_observations hPm hQm
    ((hX.adapted (s + t)).mono (G.le (s + t))).measurable
    ((hY.adapted (s + t)).mono (F.le (s + t))).measurable
  intro E hE f
  let K : Z → ℝ := fun z => reversibleResistanceTransition A t f
    (projIcc A.source.left A.source.right A.source.increasing.le (p z)).val
  have hK : Measurable K := (reversibleResistanceTransition_measurable_interval A t f.continuous.measurable).comp
    (continuous_projIcc.measurable.comp hp)
  have hKP (ω : Ω) : K (P ω) = reversibleResistanceTransition A t f (X s ω) := by
    dsimp only [K]
    rw [hPX ω, projIcc_of_mem A.source.increasing.le (hX.path_mem s ω)]
  have hKQ (ω : Ω') : K (Q ω) = reversibleResistanceTransition A t f (Y s ω) := by
    dsimp only [K]
    rw [hQY ω, projIcc_of_mem A.source.increasing.le (hY.path_mem s ω)]
  calc
    _ = ∫ ω in P ⁻¹' E, reversibleResistanceTransition A t f (X s ω) ∂μ :=
      hX.markov_setIntegral f s t (hP hE)
    _ = ∫ ω in P ⁻¹' E, K (P ω) ∂μ :=
      integral_congr_ae (Eventually.of_forall (fun ω => (hKP ω).symm))
    _ = ∫ z in E, K z ∂μ.map P := (setIntegral_map hE hK.aestronglyMeasurable hPm.aemeasurable).symm
    _ = ∫ z in E, K z ∂ν.map Q := congrArg (fun ρ : Measure Z => ∫ z in E, K z ∂ρ) hpast
    _ = ∫ ω in Q ⁻¹' E, K (Q ω) ∂ν := setIntegral_map hE hK.aestronglyMeasurable hQm.aemeasurable
    _ = ∫ ω in Q ⁻¹' E, reversibleResistanceTransition A t f (Y s ω) ∂ν :=
      integral_congr_ae (Eventually.of_forall hKQ)
    _ = _ := (hY.markov_setIntegral f s t (hQ hE)).symm

end TimeTraps.Probability

end
