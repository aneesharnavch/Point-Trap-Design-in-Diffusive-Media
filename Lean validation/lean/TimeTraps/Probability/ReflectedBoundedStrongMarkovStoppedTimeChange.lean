module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovStoppedTimeChangeData

@[expose] public section

/-! Strong Markov conditional expectations of the literal reflected
positive-clock process at every finite physical stopping time. The
reference stopping law is transferred using the proved clock restart
identity and the proved inclusion of stopped sigma-fields. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem finiteNNRealStoppingTime_add {Ω : Type*} {mΩ : MeasurableSpace Ω}
    {G : Filtration ℝ≥0 mΩ} {σ : Ω → ℝ≥0}
    (hσ : IsStoppingTime G (fun ω => (σ ω : WithTop ℝ≥0))) (t : ℝ≥0) :
    IsStoppingTime G (fun ω => ((σ ω + t : ℝ≥0) : WithTop ℝ≥0)) := by
  intro r
  by_cases ht : t ≤ r
  · have he : {ω | ((σ ω + t : ℝ≥0) : WithTop ℝ≥0) ≤ r} =
        {ω | (σ ω : WithTop ℝ≥0) ≤ (r - t : ℝ≥0)} := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe]
      exact (le_tsub_iff_right ht).symm
    rw [he]
    exact G.mono tsub_le_self _ (hσ (r - t))
  · have he : {ω | ((σ ω + t : ℝ≥0) : WithTop ℝ≥0) ≤ r} = ∅ := by
      ext ω
      simp only [mem_ofPred_eq, WithTop.coe_le_coe, mem_empty_iff_false, iff_false]
      exact fun hr => ht ((le_add_of_nonneg_left bot_le).trans hr)
    rw [he]
    exact @MeasurableSet.empty _ (G r)

theorem reflectedTimeChangedTrajectory_stopped_future_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (brownianInverseClockFiltration L hL D x c hc hpos)
      (fun ω => (σ ω : WithTop ℝ≥0))) (t : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    Integrable (fun ω => f (reflectedTimeChangedTrajectory L D x c (σ ω + t) ω))
      brownianCompletedMeasure :=
  reflectedTimeChangedTrajectory_stopped_integrable L hL D x c hc hpos
    (finiteNNRealStoppingTime_add hσ t) hf hb

theorem reflectedTimeChangedOperator_stopped_stronglyMeasurable
    (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (brownianInverseClockFiltration L hL D x c hc hpos)
      (fun ω => (σ ω : WithTop ℝ≥0))) (t : ℝ≥0) {f : ℝ → ℝ} (hf : Measurable f) :
    StronglyMeasurable[hσ.measurableSpace] (fun ω => reflectedTimeChangedOperator L D c t f
      (reflectedTimeChangedTrajectory L D x c (σ ω) ω)) := by
  let z : BrownianCompletedSample → Icc (0 : ℝ) L := fun ω =>
    ⟨reflectedTimeChangedTrajectory L D x c (σ ω) ω,
      foldedTrajectory_mem L hL D x brownianDyadicPath
        (reflectedPositiveTimeInversePath L D x c (σ ω) ω) ω⟩
  have hz : Measurable[hσ.measurableSpace] z :=
    (reflectedTimeChangedTrajectory_stopped_stronglyMeasurable L hL D x c hc hpos hσ
      measurable_id).measurable.subtype_mk
  exact ((reflectedTimeChangedOperator_measurable_interval L hL D c hc hpos t hf).comp hz).stronglyMeasurable

theorem reflectedTimeChangedTrajectory_strongMarkov
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (brownianInverseClockFiltration L hL D x c hc hpos)
      (fun ω => (σ ω : WithTop ℝ≥0))) (t : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    brownianCompletedMeasure[(fun ω => f (reflectedTimeChangedTrajectory L D x c (σ ω + t) ω)) |
      hσ.measurableSpace] =ᵐ[brownianCompletedMeasure]
        (fun ω => reflectedTimeChangedOperator L D c t f (reflectedTimeChangedTrajectory L D x c (σ ω) ω)) := by
  obtain ⟨a, ha, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  let m : ℝ≥0 := ⟨c a, (hpos a ha).le⟩
  have hm : 0 < m := hpos a ha
  have hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y := fun y hy => hmin hy
  let H := t / m
  let τ := fun ω => reflectedPositiveTimeInversePath L D x c (σ ω) ω
  have hτ := brownianInverseClock_sampled_isStoppingTime L hL D x c hc hpos hσ
  let g := reflectedTimeChangedPathTest L hL H c hc hpos t f
  have hg : Measurable g := reflectedTimeChangedPathTest_measurable L hL H c hc hpos t hf
  have hgb : ∀ p, |g p| ≤ M := fun p => hb _
  have hce := reflectedMarkovFuturePath_strongMarkov L hL D hD x H hτ hg hgb
  have hleft : (fun ω => g (reflectedMarkovFuturePath L hL D x H τ ω)) =ᵐ[brownianCompletedMeasure]
      (fun ω => f (reflectedTimeChangedTrajectory L D x c (σ ω + t) ω)) :=
    (reflectedMarkovPathTimeChange_stopped_future_actual L hL D x H c hc hpos m hm hmc
      σ t le_rfl).mono (fun ω hω => congrArg f hω)
  have hright : (fun ω => reflectedMarkovPathOperator L hL D H g
      (reflectedMarkovState L hL D x (τ ω) ω)) =ᵐ[brownianCompletedMeasure]
      (fun ω => reflectedTimeChangedOperator L D c t f (reflectedTimeChangedTrajectory L D x c (σ ω) ω)) := by
    filter_upwards [reflectedMarkovState_actual_ae L hL D x] with ω hω
    exact (reflectedTimeChangedOperator_path L hL D H c hc hpos m hm hmc t le_rfl f
      (reflectedMarkovState L hL D x (τ ω) ω)).trans
        (congrArg (reflectedTimeChangedOperator L D c t f) (hω (τ ω)))
  have href := (condExp_congr_ae hleft.symm).trans (hce.trans hright)
  have hle := brownianInverseClock_sampled_measurableSpace_le L hL D x c hc hpos hσ
  have hsm := reflectedTimeChangedOperator_stopped_stronglyMeasurable L hL D x c hc hpos hσ t hf
  have hi : Integrable (fun ω => reflectedTimeChangedOperator L D c t f
      (reflectedTimeChangedTrajectory L D x c (σ ω) ω)) brownianCompletedMeasure := by
    apply (integrable_const M).mono' (hsm.mono hσ.measurableSpace_le).aestronglyMeasurable
    exact Eventually.of_forall (fun ω => reflectedTimeChangedOperator_bound L D c t hb _)
  exact (condExp_condExp_of_le hle hτ.measurableSpace_le).symm.trans
    ((condExp_congr_ae href).trans (EventuallyEq.of_eq
      (condExp_of_stronglyMeasurable hσ.measurableSpace_le hsm hi)))

theorem reflectedTimeChangedTrajectory_strongMarkov_setIntegral
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (brownianInverseClockFiltration L hL D x c hc hpos)
      (fun ω => (σ ω : WithTop ℝ≥0))) (t : ℝ≥0)
    {f : ℝ → ℝ} (hf : Measurable f) {M : ℝ} (hb : ∀ y, |f y| ≤ M)
    {E : Set BrownianCompletedSample} (hE : MeasurableSet[hσ.measurableSpace] E) :
    (∫ ω in E, reflectedTimeChangedOperator L D c t f
      (reflectedTimeChangedTrajectory L D x c (σ ω) ω) ∂brownianCompletedMeasure) =
      ∫ ω in E, f (reflectedTimeChangedTrajectory L D x c (σ ω + t) ω) ∂brownianCompletedMeasure :=
  (integral_congr_ae ((reflectedTimeChangedTrajectory_strongMarkov L hL D hD x c hc hpos hσ t hf hb).symm.filter_mono
    ae_restrict_le)).trans (setIntegral_condExp hσ.measurableSpace_le
      (reflectedTimeChangedTrajectory_stopped_future_integrable L hL D x c hc hpos hσ t hf hb) hE)

end TimeTraps.Probability

end
