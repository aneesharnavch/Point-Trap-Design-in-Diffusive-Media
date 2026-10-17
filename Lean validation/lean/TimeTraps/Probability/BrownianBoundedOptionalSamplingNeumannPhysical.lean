module

public import TimeTraps.Probability.BrownianBoundedOptionalSamplingAdaptation
public import TimeTraps.Probability.ReversibleResistanceTimeChangeSubstitution

@[expose] public section

/-! The martingale problem for the actual inverse-clock reflected path.
The compensator is in physical time with generator D/c times the
second spatial derivative, and the initial value is the actual folded
starting point. The speed is only continuous and strictly positive. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

noncomputable def reflectedTimeChangedNeumannDynkin {L : ℝ} (F : ReflectedNeumannC2 L)
    (D x : ℝ) (c : ℝ → ℝ) (t : ℝ≥0) (ω : BrownianCompletedSample) : ℝ :=
  F.value (foldedTrajectory L D x brownianDyadicPath
    (reflectedPositiveTimeInversePath L D x c t ω) ω) - F.value (reflectedFold L x) -
      D * ∫ r in (0 : ℝ)..t.val,
        F.curvature (foldedTrajectory L D x brownianDyadicPath
          (reflectedPositiveTimeInversePath L D x c r.toNNReal ω) ω) /
            c (foldedTrajectory L D x brownianDyadicPath
              (reflectedPositiveTimeInversePath L D x c r.toNNReal ω) ω)

theorem reflectedTimeChangedNeumannDynkin_eq_sampled_ae {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    ∀ᵐ ω ∂brownianCompletedMeasure, ∀ t,
      reflectedTimeChangedNeumannDynkin F D x c t ω =
        reflectedInverseClockNeumannDynkin F hL D x c t ω := by
  filter_upwards [brownianDyadic_regular_ae, brownianDyadicPath_start_zero] with ω hω hzero
  intro t
  have hi := reflectedPositiveTimeInversePath_integral_reciprocal L hL D x c hc hpos hω
    (fun s => F.curvature (foldedTrajectory L D x brownianDyadicPath s ω)) t
  have hz : brownianDyadicPath 0 (ω : ℕ → ℝ) = 0 := hzero
  have hstart : foldedTrajectory L D x brownianDyadicPath 0 (ω : ℕ → ℝ) = reflectedFold L x := by
    exact congrArg (reflectedFold L) (by rw [hz]; ring)
  change F.value (foldedTrajectory L D x brownianDyadicPath
    (reflectedPositiveTimeInversePath L D x c t (ω : ℕ → ℝ)) (ω : ℕ → ℝ)) -
    F.value (reflectedFold L x) - D * _ =
    F.value (foldedTrajectory L D x brownianDyadicPath
      (reflectedPositiveTimeInversePath L D x c t (ω : ℕ → ℝ)) (ω : ℕ → ℝ)) -
      F.value (foldedTrajectory L D x brownianDyadicPath 0 (ω : ℕ → ℝ)) - D * _
  rw [hstart]
  exact congrArg (fun z : ℝ =>
    F.value (foldedTrajectory L D x brownianDyadicPath
      (reflectedPositiveTimeInversePath L D x c t (ω : ℕ → ℝ)) (ω : ℕ → ℝ)) -
      F.value (reflectedFold L x) - D * z) hi.symm


theorem reflectedTimeChangedNeumannDynkin_integrable_mean {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) (t : ℝ≥0) :
    Integrable (reflectedTimeChangedNeumannDynkin F D x c t) brownianCompletedMeasure ∧
      (∫ ω, reflectedTimeChangedNeumannDynkin F D x c t ω ∂brownianCompletedMeasure) = 0 := by
  have he := (reflectedTimeChangedNeumannDynkin_eq_sampled_ae F hL D x c hc hpos).mono
    (fun ω hω => hω t)
  obtain ⟨hi, hz⟩ := reflectedInverseClockNeumannDynkin_integrable_mean F hL D hD x c hc hpos t
  exact ⟨hi.congr (EventuallyEq.symm he), (integral_congr_ae he).trans hz⟩

theorem reflectedTimeChangedNeumannDynkin_stronglyAdapted {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    StronglyAdapted (brownianInverseClockFiltration L hL D x c hc hpos)
      (reflectedTimeChangedNeumannDynkin F D x c) := by
  intro t
  exact brownianCompletedStopped_stronglyMeasurable_congr
    (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos t)
    (reflectedInverseClockNeumannDynkin_stronglyAdapted F hL D hD x c hc hpos t)
    ((reflectedTimeChangedNeumannDynkin_eq_sampled_ae F hL D x c hc hpos).mono (fun ω hω => hω t))

theorem reflectedTimeChangedNeumannDynkin_condExp {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianCompletedMeasure[reflectedTimeChangedNeumannDynkin F D x c t |
      brownianInverseClockFiltration L hL D x c hc hpos s]
      =ᵐ[brownianCompletedMeasure] reflectedTimeChangedNeumannDynkin F D x c s := by
  have he := reflectedTimeChangedNeumannDynkin_eq_sampled_ae F hL D x c hc hpos
  exact (condExp_congr_ae (he.mono (fun ω hω => hω t))).trans
    ((reflectedInverseClockNeumannDynkin_condExp F hL D hD x c hc hpos hst).trans
      (EventuallyEq.symm (he.mono (fun ω hω => hω s))))

theorem reflectedTimeChangedNeumannDynkin_martingale {L : ℝ} (F : ReflectedNeumannC2 L)
    (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (c : ℝ → ℝ)
    (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    Martingale (reflectedTimeChangedNeumannDynkin F D x c)
      (brownianInverseClockFiltration L hL D x c hc hpos) brownianCompletedMeasure :=
  ⟨reflectedTimeChangedNeumannDynkin_stronglyAdapted F hL D hD x c hc hpos,
    fun _ _ hst => reflectedTimeChangedNeumannDynkin_condExp F hL D hD x c hc hpos hst⟩

end TimeTraps.Probability
