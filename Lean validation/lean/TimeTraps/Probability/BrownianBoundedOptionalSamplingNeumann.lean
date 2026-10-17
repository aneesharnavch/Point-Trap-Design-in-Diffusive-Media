module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingInverseMartingale
public import TimeTraps.Probability.ReflectedNeumannItoFormula

@[expose] public section

/-! Sampling the actual full C² Neumann Dynkin expression at inverse
clock times. The simultaneous compact-time Itô identity permits the
random-time substitution. Deterministic inverse bounds and proved
optional sampling give its conditional law and zero expectation. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def reflectedInverseClockNeumannDynkin {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ) (t : ℝ≥0) (ω : BrownianCompletedSample) : ℝ :=
  reflectedNeumannDynkin F hL brownianDyadicPath D x
    (reflectedPositiveTimeInversePath L D x c t ω) ω

theorem reflectedInverseClockNeumannDynkin_eq_integral_ae {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ t ≤ T,
      reflectedInverseClockNeumannDynkin F hL D x c t ω =
        brownianInverseClockIntegral (reflectedNeumannItoIntegrand F hL D x (T / m))
          L D x c t ω := by
  filter_upwards [reflectedNeumannDynkin_eq_ito_continuous_ae F hL D hD x (T / m)] with ω hω
  intro t ht
  exact hω _ ((reflectedPositiveTimeInversePath_bound L hL D x c hc hpos m hm hmc t ω).trans
    (div_le_div_of_nonneg_right ht (show 0 ≤ m from zero_le)))

theorem reflectedInverseClockNeumannDynkin_integrable_mean {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (t : ℝ≥0) :
    Integrable (reflectedInverseClockNeumannDynkin F hL D x c t) brownianCompletedMeasure ∧
      (∫ ω, reflectedInverseClockNeumannDynkin F hL D x c t ω ∂brownianCompletedMeasure) = 0 := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  let m : ℝ≥0 := ⟨c y, (hpos y hy).le⟩
  have he := (reflectedInverseClockNeumannDynkin_eq_integral_ae F hL D hD x c hc hpos
    m (hpos y hy) (fun z hz => hmin hz) t).mono (fun ω hω => hω t le_rfl)
  obtain ⟨hi, hz⟩ := brownianInverseClockIntegral_integrable_mean
    (reflectedNeumannItoIntegrand F hL D x (t / m)) L hL D x c hc hpos t
  exact ⟨hi.congr (EventuallyEq.symm he), (integral_congr_ae he).trans hz⟩

theorem reflectedInverseClockNeumannDynkin_condExp {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianCompletedMeasure[reflectedInverseClockNeumannDynkin F hL D x c t |
      brownianInverseClockFiltration L hL D x c hc hpos s]
      =ᵐ[brownianCompletedMeasure] reflectedInverseClockNeumannDynkin F hL D x c s := by
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn
    (show (Icc (0 : ℝ) L).Nonempty from ⟨0, le_rfl, hL.le⟩) hc
  let m : ℝ≥0 := ⟨c y, (hpos y hy).le⟩
  have he := reflectedInverseClockNeumannDynkin_eq_integral_ae F hL D hD x c hc hpos
    m (hpos y hy) (fun z hz => hmin hz) t
  exact (condExp_congr_ae (he.mono (fun ω hω => hω t le_rfl))).trans
    ((brownianInverseClockIntegral_condExp (reflectedNeumannItoIntegrand F hL D x (t / m))
      L hL D x c hc hpos hst).trans (EventuallyEq.symm (he.mono (fun ω hω => hω s hst))))

theorem reflectedInverseClockNeumannDynkin_eq_literal_ae {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ t,
      reflectedInverseClockNeumannDynkin F hL D x c t ω =
        reflectedNeumannDynkin F hL brownianDyadicPath D x
          (reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω) ω := by
  filter_upwards [reflectedPositiveTimeInversePath_eq_ae L D x c] with ω hω
  intro t
  unfold reflectedInverseClockNeumannDynkin
  rw [hω t]

end TimeTraps.Probability
