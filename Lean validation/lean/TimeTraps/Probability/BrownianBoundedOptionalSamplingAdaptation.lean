module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingNeumann

@[expose] public section

/-! Every stopped sigma-field of the augmented Brownian filtration
contains all ambient null sets. Consequently the actual expressions,
not only their almost-everywhere representatives, inherit strong
adaptation from the continuous stochastic integral. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem brownianCompletedStopped_measurableSet_null
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    {A : Set BrownianCompletedSample} (hA : A =ᵐ[brownianCompletedMeasure] (∅ : Set BrownianCompletedSample)) :
    MeasurableSet[hτ.measurableSpace] A := by
  have h0 : MeasurableSet[brownianCompletedFiltration 0] A := by
    refine ⟨∅, ?_, hA⟩
    exact @MeasurableSet.empty _ (brownianNaturalFiltration brownianDyadicPath
      brownianDyadicPath_measurable 0)
  exact hτ.le_measurableSpace_of_const_le
    (fun ω => show (0 : ℝ≥0) ≤ (τ ω : WithTop ℝ≥0) from WithTop.coe_le_coe.mpr zero_le)
    A (brownianCompletedFiltration.le_rightCont 0 A h0)

theorem brownianCompletedStopped_measurableSet_congr
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    {A C : Set BrownianCompletedSample} (hC : MeasurableSet[hτ.measurableSpace] C)
    (he : A =ᵐ[brownianCompletedMeasure] C) : MeasurableSet[hτ.measurableSpace] A := by
  have hAC : MeasurableSet[hτ.measurableSpace] (A \ C) := by
    apply brownianCompletedStopped_measurableSet_null hτ
    exact (he.diff (EventuallyEq.refl _ C)).trans (Eventually.of_forall (by simp))
  have hCA : MeasurableSet[hτ.measurableSpace] (C \ A) := by
    apply brownianCompletedStopped_measurableSet_null hτ
    exact (he.symm.diff (EventuallyEq.refl _ A)).trans (Eventually.of_forall (by simp))
  have hset : A = (C \ (C \ A)) ∪ (A \ C) := by
    ext ω
    simp only [mem_union, Set.mem_sdiff]
    tauto
  rw [hset]
  exact (hC.diff hCA).union hAC

theorem brownianCompletedStopped_stronglyMeasurable_congr
    {τ : BrownianCompletedSample → ℝ≥0}
    (hτ : IsStoppingTime brownianCompletedFiltration.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    {f g : BrownianCompletedSample → ℝ} (hf : StronglyMeasurable[hτ.measurableSpace] f)
    (he : g =ᵐ[brownianCompletedMeasure] f) : StronglyMeasurable[hτ.measurableSpace] g := by
  apply Measurable.stronglyMeasurable
  intro A hA
  exact brownianCompletedStopped_measurableSet_congr hτ (hf.measurable hA) (he.preimage A)

theorem reflectedInverseClockNeumannDynkin_stronglyAdapted {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    StronglyAdapted (brownianInverseClockFiltration L hL D x c hc hpos)
      (reflectedInverseClockNeumannDynkin F hL D x c) := by
  intro t
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  let m : ℝ≥0 := ⟨c y, (hpos y hy).le⟩
  exact brownianCompletedStopped_stronglyMeasurable_congr
    (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t)
    (brownianInverseClockIntegral_stronglyAdapted (reflectedNeumannItoIntegrand F hL D x (t / m))
      L hL D x c hc hpos t)
    ((reflectedInverseClockNeumannDynkin_eq_integral_ae F hL D hD x c hc hpos m (hpos y hy)
      (fun z hz => hmin hz) t).mono (fun ω hω => hω t le_rfl))

theorem reflectedInverseClockNeumannDynkin_martingale {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    Martingale (reflectedInverseClockNeumannDynkin F hL D x c)
      (brownianInverseClockFiltration L hL D x c hc hpos) brownianCompletedMeasure :=
  ⟨reflectedInverseClockNeumannDynkin_stronglyAdapted F hL D hD x c hc hpos,
    fun _ _ hst => reflectedInverseClockNeumannDynkin_condExp F hL D hD x c hc hpos hst⟩

end TimeTraps.Probability
