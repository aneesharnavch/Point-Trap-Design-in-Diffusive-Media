module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovTimeChangeKernel

@[expose] public section

/-! The actual positive-clock reflected process is Markov in its explicit
inverse-clock filtration. This conditional law is derived from the full
reference future-path strong Markov law and the literal integral-clock
restart identity, without a martingale-problem uniqueness premise. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal

theorem reflectedTimeChangedTrajectory_stronglyMeasurable
    (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) :
    StronglyMeasurable[brownianInverseClockFiltration L hL D x c hc hpos t]
      (fun ω => f (reflectedTimeChangedTrajectory L D x c t ω)) :=
  foldedTrajectory_completed_borel_stopped_stronglyMeasurable L hL D x
    (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t) hf

theorem reflectedTimeChangedTrajectory_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    Integrable (fun ω => f (reflectedTimeChangedTrajectory L D x c t ω)) brownianCompletedMeasure :=
  foldedTrajectory_completed_borel_stopped_integrable L hL D x
    (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t) hf hb

theorem reflectedTimeChangedTrajectory_markov
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (s t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    brownianCompletedMeasure[(fun ω => f (reflectedTimeChangedTrajectory L D x c (s + t) ω)) |
      brownianInverseClockFiltration L hL D x c hc hpos s] =ᵐ[brownianCompletedMeasure]
        (fun ω => reflectedTimeChangedOperator L D c t f (reflectedTimeChangedTrajectory L D x c s ω)) := by
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  let m : ℝ≥0 := ⟨c a, (hpos a ha).le⟩
  have hm : 0 < m := hpos a ha
  have hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y := fun y hy => hmin hy
  let H := t / m
  let τ := reflectedPositiveTimeInversePath L D x c s
  have hτ := brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos s
  let g := reflectedTimeChangedPathTest L hL H c hc hpos t f
  have hg : Measurable g := reflectedTimeChangedPathTest_measurable L hL H c hc hpos t hf
  have hgb : ∀ p, |g p| ≤ M := fun p => hb _
  have hce := reflectedMarkovFuturePath_strongMarkov L hL D hD x H hτ hg hgb
  have hleft : (fun ω => g (reflectedMarkovFuturePath L hL D x H τ ω)) =ᵐ[brownianCompletedMeasure]
      (fun ω => f (reflectedTimeChangedTrajectory L D x c (s + t) ω)) :=
    (reflectedMarkovPathTimeChange_future_actual L hL D x H c hc hpos m hm hmc s t le_rfl).mono
      (fun ω hω => congrArg f hω)
  have hright : (fun ω => reflectedMarkovPathOperator L hL D H g
      (reflectedMarkovState L hL D x (τ ω) ω)) =ᵐ[brownianCompletedMeasure]
      (fun ω => reflectedTimeChangedOperator L D c t f (reflectedTimeChangedTrajectory L D x c s ω)) := by
    filter_upwards [reflectedMarkovState_actual_ae L hL D x] with ω hω
    exact (reflectedTimeChangedOperator_path L hL D H c hc hpos m hm hmc t le_rfl f
      (reflectedMarkovState L hL D x (τ ω) ω)).trans
        (congrArg (reflectedTimeChangedOperator L D c t f) (hω (τ ω)))
  exact (condExp_congr_ae hleft.symm).trans (hce.trans hright)

theorem reflectedTimeChangedTrajectory_markov_setIntegral
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (s t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M)
    {A : Set BrownianCompletedSample}
    (hA : MeasurableSet[brownianInverseClockFiltration L hL D x c hc hpos s] A) :
    (∫ ω in A, reflectedTimeChangedOperator L D c t f
      (reflectedTimeChangedTrajectory L D x c s ω) ∂brownianCompletedMeasure) =
      ∫ ω in A, f (reflectedTimeChangedTrajectory L D x c (s + t) ω) ∂brownianCompletedMeasure :=
  (integral_congr_ae ((reflectedTimeChangedTrajectory_markov L hL D hD x c hc hpos s t hf hb).symm.filter_mono
    ae_restrict_le)).trans (setIntegral_condExp ((brownianInverseClockFiltration L hL D x c hc hpos).le s)
      (reflectedTimeChangedTrajectory_integrable L hL D x c hc hpos (s + t) hf hb) hA)

end TimeTraps.Probability

end
