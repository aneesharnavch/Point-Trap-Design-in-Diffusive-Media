module

public import TimeTraps.Probability.ReflectedBoundedStrongMarkovPathClockPrefix
public import TimeTraps.Probability.ReflectedBoundedStrongMarkovClockData
public import TimeTraps.Probability.BrownianBoundedOptionalSamplingInverseMartingale

@[expose] public section

/-! The finite-path clock functional agrees with the literal reflected
inverse-clock trajectory. Uniform bounds follow from the original
positive compact spatial speed; the actual inverse and restart identities
hold on the existing all-time Brownian regular event. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal

def reflectedTimeChangedTrajectory (L D x : ℝ) (c : ℝ → ℝ)
    (t : ℝ≥0) (ω : BrownianCompletedSample) : ℝ :=
  foldedTrajectory L D x brownianDyadicPath (reflectedPositiveTimeInversePath L D x c t ω) ω

theorem reflectedPositiveTimeSpeed_lower_bound (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y)
    (ω : BrownianCompletedSample) (hω : BrownianDyadicRegular ω) :
    m ≤ (reflectedPositiveTimeSpeed L hL D x brownianDyadicPath c hc hpos ω hω.continuous).lower := by
  obtain ⟨⟨y, hy, he, _⟩, _⟩ :=
    reflectedPositiveTimeSpeed_extrema L hL D x brownianDyadicPath c hc hpos ω hω.continuous
  exact (hmc y hy).trans_eq he

theorem reflectedMarkovPathTimeChange_future_prefix
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y)
    (t : ℝ≥0) (ht : t / m ≤ H) (τ : BrownianCompletedSample → ℝ≥0)
    (ω : BrownianCompletedSample) (hω : BrownianDyadicRegular ω) :
    (reflectedMarkovPathTimeChange L hL H (fun y : Icc (0 : ℝ) L => c y.val)
      hc.domRestrict (fun y => hpos y.val y.property) t
        (reflectedMarkovFuturePath L hL D x H τ ω)).val =
      foldedTrajectory L D x brownianDyadicPath
        (τ ω + ((reflectedPositiveTimeSpeed L hL D x brownianDyadicPath c hc hpos
          ω hω.continuous).restart (τ ω)).inverse t) ω := by
  let v := reflectedPositiveTimeSpeed L hL D x brownianDyadicPath c hc hpos ω hω.continuous
  let Y : ℝ≥0 → Icc (0 : ℝ) L := fun r =>
    ⟨foldedTrajectory L D x brownianDyadicPath (τ ω + r) ω,
      foldedTrajectory_mem L hL D x brownianDyadicPath (τ ω + r) ω⟩
  have hp (r : Icc (0 : ℝ≥0) H) :
      reflectedMarkovFuturePath L hL D x H τ ω r = Y r.val := by
    apply Subtype.ext
    change reflectedFold L (x + Real.sqrt (2 * D) * reflectedMarkovBrownianPath (τ ω + r.val) ω) = _
    rw [reflectedMarkovBrownianPath, if_pos hω]
    rfl
  have htime : (v.restart (τ ω)).inverse t ≤ H :=
    ((v.restart (τ ω)).inverse_bounds t).2.trans
      ((div_le_div_of_nonneg_left (show 0 ≤ t from bot_le) hm
        (reflectedPositiveTimeSpeed_lower_bound L hL D x c hc hpos m hmc ω hω)).trans ht)
  exact congrArg Subtype.val (reflectedMarkovPathTimeChange_agrees L hL H
    (fun y : Icc (0 : ℝ) L => c y.val) hc.domRestrict (fun y => hpos y.val y.property)
    (reflectedMarkovFuturePath L hL D x H τ ω) (v.restart (τ ω)) Y (fun _ => rfl) hp htime)

theorem reflectedMarkovPathTimeChange_fresh_actual
    (L : ℝ) (hL : 0 < L) (D : ℝ) (H : ℝ≥0)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y)
    (t : ℝ≥0) (ht : t / m ≤ H) (y : Icc (0 : ℝ) L) :
    ∀ᵐ ω ∂brownianCompletedMeasure,
      (reflectedMarkovPathTimeChange L hL H (fun y : Icc (0 : ℝ) L => c y.val)
        hc.domRestrict (fun y => hpos y.val y.property) t
          (reflectedMarkovFreshPath L hL D H (y, ω))).val =
        reflectedTimeChangedTrajectory L D y.val c t ω := by
  have hr : ∀ᵐ ω ∂brownianCompletedMeasure, BrownianDyadicRegular ω := brownianDyadic_regular_ae
  filter_upwards [hr] with ω hω
  let v := reflectedPositiveTimeSpeed L hL D y.val brownianDyadicPath c hc hpos ω hω.continuous
  have he := reflectedMarkovPathTimeChange_future_prefix L hL D y.val H c hc hpos
    m hm hmc t ht (fun _ => 0) ω hω
  have hinv : (v.restart 0).inverse t = v.inverse t := by
    have h := v.inverse_restart 0 t
    simpa only [v.clock_zero, zero_add] using h.symm
  have ha : reflectedPositiveTimeInversePath L D y.val c t ω = v.inverse t := by
    have hi : reflectedPositiveTimeInversePath L D y.val c t ω =
        reflectedPositiveTimeInverse L D y.val brownianDyadicPath c t ω := if_pos hω
    exact hi.trans (congrFun (reflectedPositiveTimeInverse_eq L hL D y.val brownianDyadicPath c hc hpos
      ω hω.continuous) t)
  change _ = foldedTrajectory L D y.val brownianDyadicPath
    (reflectedPositiveTimeInversePath L D y.val c t ω) ω
  simp only [zero_add] at he
  change _ = foldedTrajectory L D y.val brownianDyadicPath ((v.restart 0).inverse t) ω at he
  exact he.trans ((congrArg (fun r => foldedTrajectory L D y.val brownianDyadicPath r ω) hinv).trans
    (congrArg (fun r => foldedTrajectory L D y.val brownianDyadicPath r ω) ha.symm))

theorem reflectedMarkovPathTimeChange_future_actual
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (H : ℝ≥0)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y)
    (s t : ℝ≥0) (ht : t / m ≤ H) :
    ∀ᵐ ω ∂brownianCompletedMeasure,
      (reflectedMarkovPathTimeChange L hL H (fun y : Icc (0 : ℝ) L => c y.val)
        hc.domRestrict (fun y => hpos y.val y.property) t
          (reflectedMarkovFuturePath L hL D x H
            (reflectedPositiveTimeInversePath L D x c s) ω)).val =
        reflectedTimeChangedTrajectory L D x c (s + t) ω := by
  have hr : ∀ᵐ ω ∂brownianCompletedMeasure, BrownianDyadicRegular ω := brownianDyadic_regular_ae
  filter_upwards [hr] with ω hω
  let v := reflectedPositiveTimeSpeed L hL D x brownianDyadicPath c hc hpos ω hω.continuous
  have ha (r : ℝ≥0) : reflectedPositiveTimeInversePath L D x c r ω = v.inverse r := by
    have hi : reflectedPositiveTimeInversePath L D x c r ω =
        reflectedPositiveTimeInverse L D x brownianDyadicPath c r ω := if_pos hω
    exact hi.trans (congrFun (reflectedPositiveTimeInverse_eq L hL D x brownianDyadicPath c hc hpos
      ω hω.continuous) r)
  have he := reflectedMarkovPathTimeChange_future_prefix L hL D x H c hc hpos m hm hmc
    t ht (reflectedPositiveTimeInversePath L D x c s) ω hω
  change _ = foldedTrajectory L D x brownianDyadicPath
    (reflectedPositiveTimeInversePath L D x c (s + t) ω) ω
  exact he.trans ((congrArg (fun r => foldedTrajectory L D x brownianDyadicPath
    (r + (v.restart r).inverse t) ω) (ha s)).trans
      ((congrArg (fun r => foldedTrajectory L D x brownianDyadicPath r ω) (v.inverse_add s t).symm).trans
        (congrArg (fun r => foldedTrajectory L D x brownianDyadicPath r ω) (ha (s + t)).symm)))

end TimeTraps.Probability

end
