module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovStoppingClock

@[expose] public section

/-! A finite physical stopping time yields a genuine stopping time of
the completed reference filtration. The actual time-changed trajectory
is continuous on every sample, adapted at physical stopping times, and
agrees with the measurable future-path clock functional on one common
Brownian regular event. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem brownianInverseClock_sampled_isStoppingTime
    (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (brownianInverseClockFiltration L hL D x c hc hpos)
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    IsStoppingTime brownianCompletedFiltration.rightCont
      (fun ω => (reflectedPositiveTimeInversePath L D x c (σ ω) ω : WithTop ℝ≥0)) :=
  sampledClock_isStoppingTime (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos)
    (fun _ => rfl) (reflectedPositiveTimeInversePath_monotone L hL D x c hc hpos)
      (reflectedPositiveTimeInversePath_continuous L hL D x c hc hpos) hσ

theorem brownianInverseClock_sampled_measurableSpace_le
    (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (brownianInverseClockFiltration L hL D x c hc hpos)
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    hσ.measurableSpace ≤
      (brownianInverseClock_sampled_isStoppingTime L hL D x c hc hpos hσ).measurableSpace :=
  sampledClock_stopped_measurableSpace_le
    (brownianCompletedInversePath_isStoppingTime L hL D x c hc hpos)
    (fun _ => rfl) (reflectedPositiveTimeInversePath_monotone L hL D x c hc hpos)
      (reflectedPositiveTimeInversePath_continuous L hL D x c hc hpos) hσ

theorem reflectedTimeChangedTrajectory_continuous
    (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (ω : BrownianCompletedSample) : Continuous (fun t => reflectedTimeChangedTrajectory L D x c t ω) := by
  by_cases hω : BrownianDyadicRegular ω
  · exact ((reflectedFold_continuous L).comp
      (continuous_const.add (continuous_const.mul hω.continuous))).comp
        (reflectedPositiveTimeInversePath_continuous L hL D x c hc hpos ω)
  · simpa only [reflectedTimeChangedTrajectory, reflectedPositiveTimeInversePath, if_neg hω] using
      (continuous_const : Continuous (fun _ : ℝ≥0 => foldedTrajectory L D x brownianDyadicPath 0 ω))

theorem reflectedTimeChangedTrajectory_stopped_stronglyMeasurable
    (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (brownianInverseClockFiltration L hL D x c hc hpos)
      (fun ω => (σ ω : WithTop ℝ≥0))) {f : ℝ → ℝ} (hf : Measurable f) :
    StronglyMeasurable[hσ.measurableSpace]
      (fun ω => f (reflectedTimeChangedTrajectory L D x c (σ ω) ω)) := by
  have ha : StronglyAdapted (brownianInverseClockFiltration L hL D x c hc hpos)
      (reflectedTimeChangedTrajectory L D x c) := fun t =>
    reflectedTimeChangedTrajectory_stronglyMeasurable L hL D x c hc hpos t measurable_id
  have hm := measurable_stoppedValue
    (ha.isStronglyProgressive_of_continuous
      (reflectedTimeChangedTrajectory_continuous L hL D x c hc hpos)) hσ
  exact (hf.comp hm).stronglyMeasurable

theorem reflectedTimeChangedTrajectory_stopped_integrable
    (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    {σ : BrownianCompletedSample → ℝ≥0}
    (hσ : IsStoppingTime (brownianInverseClockFiltration L hL D x c hc hpos)
      (fun ω => (σ ω : WithTop ℝ≥0))) {f : ℝ → ℝ} (hf : Measurable f)
    {M : ℝ} (hb : ∀ y, |f y| ≤ M) :
    Integrable (fun ω => f (reflectedTimeChangedTrajectory L D x c (σ ω) ω))
      brownianCompletedMeasure := by
  apply (integrable_const M).mono'
    (((reflectedTimeChangedTrajectory_stopped_stronglyMeasurable L hL D x c hc hpos hσ hf).mono
      hσ.measurableSpace_le).aestronglyMeasurable)
  exact Eventually.of_forall (fun ω => hb (reflectedTimeChangedTrajectory L D x c (σ ω) ω))

theorem reflectedMarkovPathTimeChange_stopped_future_actual
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y)
    (σ : BrownianCompletedSample → ℝ≥0) (t : ℝ≥0) (ht : t / m ≤ H) :
    ∀ᵐ ω ∂brownianCompletedMeasure,
      (reflectedMarkovPathTimeChange L hL H (fun y : Icc (0 : ℝ) L => c y.val)
        hc.domRestrict (fun y => hpos y.val y.property) t
          (reflectedMarkovFuturePath L hL D x H
            (fun ω => reflectedPositiveTimeInversePath L D x c (σ ω) ω) ω)).val =
        reflectedTimeChangedTrajectory L D x c (σ ω + t) ω := by
  have hr : ∀ᵐ ω ∂brownianCompletedMeasure, BrownianDyadicRegular ω := brownianDyadic_regular_ae
  filter_upwards [hr] with ω hω
  let v := reflectedPositiveTimeSpeed L hL D x brownianDyadicPath c hc hpos ω hω.continuous
  have ha (r : ℝ≥0) : reflectedPositiveTimeInversePath L D x c r ω = v.inverse r := by
    have hi : reflectedPositiveTimeInversePath L D x c r ω =
        reflectedPositiveTimeInverse L D x brownianDyadicPath c r ω := if_pos hω
    exact hi.trans (congrFun (reflectedPositiveTimeInverse_eq L hL D x brownianDyadicPath c hc hpos
      ω hω.continuous) r)
  have he := reflectedMarkovPathTimeChange_future_prefix L hL D x H c hc hpos m hm hmc
    t ht (fun ω => reflectedPositiveTimeInversePath L D x c (σ ω) ω) ω hω
  change _ = foldedTrajectory L D x brownianDyadicPath
    (reflectedPositiveTimeInversePath L D x c (σ ω + t) ω) ω
  exact he.trans ((congrArg (fun r => foldedTrajectory L D x brownianDyadicPath
    (r + (v.restart r).inverse t) ω) (ha (σ ω))).trans
      ((congrArg (fun r => foldedTrajectory L D x brownianDyadicPath r ω) (v.inverse_add (σ ω) t).symm).trans
        (congrArg (fun r => foldedTrajectory L D x brownianDyadicPath r ω) (ha (σ ω + t)).symm)))

end TimeTraps.Probability

end
