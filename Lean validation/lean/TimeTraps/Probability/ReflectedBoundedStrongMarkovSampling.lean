module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovCountable

@[expose] public section

/-! Arbitrary finite stopping times are approached from above by the
countable stopping grids. The spatial test is bounded, so dominated
convergence needs no deterministic bound on the stopping time. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem reflectedMarkovObservation_upper_setIntegral_tendsto
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (f : C(Icc (0 : ℝ) L, ℝ)) (h : ℝ≥0)
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) (A : Set BrownianCompletedSample) :
    Tendsto (fun n => ∫ ω in A, reflectedMarkovObservation L hL D x f
      (boundedStoppingUpperGrid n (τ ω) + h) ω ∂brownianCompletedMeasure)
      atTop (𝓝 (∫ ω in A, reflectedMarkovObservation L hL D x f
        (τ ω + h) ω ∂brownianCompletedMeasure)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : BrownianCompletedSample => ‖f‖)
  · intro n
    exact (reflectedMarkovObservation_stopped_integrable L hL D x f
      (reflectedMarkovStoppingTime_add (boundedStoppingUpperGrid_isStoppingTime hτ n) h)).aestronglyMeasurable.restrict
  · exact integrable_const _
  · exact fun n => Eventually.of_forall (fun ω => reflectedMarkovObservation_bound L hL D x f _ ω)
  · exact Eventually.of_forall (fun ω =>
      (reflectedMarkovObservation_continuous L hL D x f ω).continuousAt.tendsto.comp
        ((boundedStoppingUpperGrid_tendsto (τ ω)).add_const h))

theorem reflectedMarkovObservation_stopping_setIntegral
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (h : ℝ≥0) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set BrownianCompletedSample} (hA : MeasurableSet[hτ.measurableSpace] A) :
    (∫ ω in A, reflectedMarkovObservation L hL D x
      (reflectedFellerTimeOperator L hL D h.val f) (τ ω) ω ∂brownianCompletedMeasure) =
      ∫ ω in A, reflectedMarkovObservation L hL D x f (τ ω + h) ω ∂brownianCompletedMeasure := by
  have he (n : ℕ) :
      (∫ ω in A, reflectedMarkovObservation L hL D x
        (reflectedFellerTimeOperator L hL D h.val f)
        (boundedStoppingUpperGrid n (τ ω)) ω ∂brownianCompletedMeasure) =
      ∫ ω in A, reflectedMarkovObservation L hL D x f
        (boundedStoppingUpperGrid n (τ ω) + h) ω ∂brownianCompletedMeasure := by
    have hstop := boundedStoppingUpperGrid_isStoppingTime hτ n
    have hle : (fun ω => (τ ω : WithTop ℝ≥0)) ≤
        (fun ω => (boundedStoppingUpperGrid n (τ ω) : WithTop ℝ≥0)) := by
      intro ω
      change (τ ω : WithTop ℝ≥0) ≤ (boundedStoppingUpperGrid n (τ ω) : WithTop ℝ≥0)
      exact_mod_cast (boundedStoppingUpperGrid_bounds n (τ ω)).1
    have hc : (range (fun ω => boundedStoppingUpperGrid n (τ ω))).Countable := by
      apply (countable_range (fun k : ℕ => (k : ℝ≥0) / ((n : ℝ≥0) + 1))).mono
      rintro _ ⟨ω, rfl⟩
      exact ⟨⌈τ ω * ((n : ℝ≥0) + 1)⌉₊, rfl⟩
    exact reflectedMarkovObservation_countable_setIntegral L hL D hD x f h hstop hc
      (hτ.measurableSpace_mono hstop hle A hA)
  have hleft := reflectedMarkovObservation_upper_setIntegral_tendsto L hL D x
    (reflectedFellerTimeOperator L hL D h.val f) 0 hτ A
  simp only [add_zero] at hleft
  have hright := reflectedMarkovObservation_upper_setIntegral_tendsto L hL D x f h hτ A
  exact tendsto_nhds_unique hleft (hright.congr (fun n => (he n).symm))

theorem reflectedMarkovObservation_stopping_condExp
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (f : C(Icc (0 : ℝ) L, ℝ)) (h : ℝ≥0) {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    brownianCompletedMeasure[
      (fun ω => reflectedMarkovObservation L hL D x f (τ ω + h) ω) | hτ.measurableSpace]
      =ᵐ[brownianCompletedMeasure] (fun ω => reflectedMarkovObservation L hL D x
        (reflectedFellerTimeOperator L hL D h.val f) (τ ω) ω) := by
  apply (ae_eq_condExp_of_forall_setIntegral_eq hτ.measurableSpace_le
    (reflectedMarkovObservation_stopped_integrable L hL D x f
      (reflectedMarkovStoppingTime_add hτ h)) _ _
    (reflectedMarkovObservation_stopped_stronglyMeasurable L hL D x
      (reflectedFellerTimeOperator L hL D h.val f) hτ).aestronglyMeasurable).symm
  · intro A _ _
    exact (reflectedMarkovObservation_stopped_integrable L hL D x
      (reflectedFellerTimeOperator L hL D h.val f) hτ).integrableOn
  · intro A hA _
    exact reflectedMarkovObservation_stopping_setIntegral L hL D hD x f h hτ hA

end TimeTraps.Probability

end
