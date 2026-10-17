module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingTimeChange

@[expose] public section

/-! The actual continuous Brownian integral sampled at the inverse of a
positive continuous reflected clock is a martingale in the stopped
filtration. Monotonicity and deterministic compact bounds are derived
from the clock, and the conditional identities use bounded optional
sampling. No time-change preservation principle is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

theorem reflectedPositiveTimeInversePath_monotone (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (ω : ℕ → ℝ) : Monotone (fun t => reflectedPositiveTimeInversePath L D x c t ω) := by
  by_cases hω : BrownianDyadicRegular ω
  · simp only [reflectedPositiveTimeInversePath, if_pos hω]
    exact (reflectedPositiveTimeChange_regular L hL D x brownianDyadicPath c hc hpos ω
      hω.continuous).2.2.2.2.1.monotone
  · simp only [reflectedPositiveTimeInversePath, if_neg hω]
    exact monotone_const

def brownianInverseClockFiltration (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    Filtration ℝ≥0 (inferInstance : MeasurableSpace BrownianCompletedSample) where
  seq t := (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t).measurableSpace
  mono' := by
    intro s t hst
    apply IsStoppingTime.measurableSpace_mono
    intro ω
    change (reflectedPositiveTimeInversePath L D x c s ω : WithTop ℝ≥0) ≤
      (reflectedPositiveTimeInversePath L D x c t ω : WithTop ℝ≥0)
    exact WithTop.coe_le_coe.mpr
      (reflectedPositiveTimeInversePath_monotone L hL D x c hc hpos ω hst)
  le' t := (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t).measurableSpace_le

def brownianInverseClockIntegral (f : BrownianIntegrand) (L D x : ℝ) (c : ℝ → ℝ)
    (t : ℝ≥0) (ω : BrownianCompletedSample) : ℝ :=
  brownianCompletedIntegralPath f (reflectedPositiveTimeInversePath L D x c t ω) ω

theorem brownianInverseClockIntegral_continuous (f : BrownianIntegrand)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (ω : BrownianCompletedSample) : Continuous (fun t => brownianInverseClockIntegral f L D x c t ω) :=
  (brownianCompletedIntegralPath_continuous f ω).comp
    (reflectedPositiveTimeInversePath_continuous L hL D x c hc hpos ω)

theorem brownianInverseClockIntegral_stronglyAdapted (f : BrownianIntegrand)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    StronglyAdapted (brownianInverseClockFiltration L hL D x c hc hpos)
      (brownianInverseClockIntegral f L D x c) :=
  fun t => brownianCompletedIntegralPath_stopped_stronglyMeasurable f
    (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t)

theorem brownianInverseClockIntegral_integrable_mean (f : BrownianIntegrand)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (t : ℝ≥0) :
    Integrable (brownianInverseClockIntegral f L D x c t) brownianCompletedMeasure ∧
      (∫ ω, brownianInverseClockIntegral f L D x c t ω ∂brownianCompletedMeasure) = 0 := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  exact brownianCompletedIntegralPath_inverse_integrable_mean f L hL D x c hc hpos
    ⟨c y, (hpos y hy).le⟩ (hpos y hy) (fun z hz => hmin hz) t

theorem brownianInverseClockIntegral_condExp (f : BrownianIntegrand)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianCompletedMeasure[brownianInverseClockIntegral f L D x c t |
      brownianInverseClockFiltration L hL D x c hc hpos s]
      =ᵐ[brownianCompletedMeasure] brownianInverseClockIntegral f L D x c s := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  exact brownianCompletedIntegralPath_optionalSampling_two f
    (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos s)
    (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t)
    (fun ω => reflectedPositiveTimeInversePath_monotone L hL D x c hc hpos ω hst)
    (reflectedPositiveTimeInversePath_bound L hL D x c hc hpos
      ⟨c y, (hpos y hy).le⟩ (hpos y hy) (fun z hz => hmin hz) t)

theorem brownianInverseClockIntegral_martingale (f : BrownianIntegrand)
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    Martingale (brownianInverseClockIntegral f L D x c)
      (brownianInverseClockFiltration L hL D x c hc hpos) brownianCompletedMeasure :=
  ⟨brownianInverseClockIntegral_stronglyAdapted f L hL D x c hc hpos,
    fun _ _ hst => brownianInverseClockIntegral_condExp f L hL D x c hc hpos hst⟩

theorem brownianInverseClockIntegral_eq_literal_ae (f : BrownianIntegrand)
    (L D x : ℝ) (c : ℝ → ℝ) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ t,
      brownianInverseClockIntegral f L D x c t ω =
        brownianIntegralGlobalPath f
          (reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ω := by
  filter_upwards [reflectedPositiveTimeInversePath_eq_ae L D x c] with ω hω
  intro t
  unfold brownianInverseClockIntegral brownianCompletedIntegralPath
  rw [hω t]

end TimeTraps.Probability

end
