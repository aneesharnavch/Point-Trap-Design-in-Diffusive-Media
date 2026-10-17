module

public import TimeTraps.Probability.ReflectedPositiveTimeChangeStopping
public import TimeTraps.Probability.BrownianIntegralCompactMaximalPath
public import TimeTraps.Probability.BrownianJointMeasurability

@[expose] public section

/-! A jointly measurable continuous-time version of the actual inverse.
It agrees with the literal inverse at all times on the proved measurable
Brownian regular event and is zero elsewhere. The raw inverse is not
silently replaced in its existing definitions or theorems. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal Topology

noncomputable def reflectedPositiveTimeInversePath (L D x : ℝ) (c : ℝ → ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ≥0 := by
  classical
  exact if BrownianDyadicRegular ω then reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω else 0

theorem reflectedPositiveTimeInversePath_continuous (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (ω : ℕ → ℝ) : Continuous (fun t => reflectedPositiveTimeInversePath L D x c t ω) := by
  by_cases hω : BrownianDyadicRegular ω
  · simp only [reflectedPositiveTimeInversePath, if_pos hω]
    exact (reflectedPositiveTimeChange_regular L hL D x brownianDyadicPath c hc hpos ω
      hω.continuous).2.2.2.1
  · simpa only [reflectedPositiveTimeInversePath, if_neg hω] using
      (continuous_const : Continuous (fun _ : ℝ≥0 => (0 : ℝ≥0)))

theorem reflectedPositiveTimeInversePath_measurable (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) : Measurable (reflectedPositiveTimeInversePath L D x c t) := by
  classical
  apply measurable_of_Iic
  intro s
  have he : (reflectedPositiveTimeInversePath L D x c t) ⁻¹' Iic s =
      {ω : ℕ → ℝ | BrownianDyadicRegular ω}ᶜ ∪
        ({ω : ℕ → ℝ | BrownianDyadicRegular ω} ∩
          {ω | t ≤ reflectedPositiveTimeClock L D x brownianDyadicPath c s ω}) := by
    ext ω
    by_cases hω : BrownianDyadicRegular ω
    · change (if BrownianDyadicRegular ω then
          reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω else 0) ≤ s ↔
        (¬BrownianDyadicRegular ω ∨ BrownianDyadicRegular ω ∧
          t ≤ reflectedPositiveTimeClock L D x brownianDyadicPath c s ω)
      rw [if_pos hω]
      simp only [hω, not_true_eq_false, true_and, false_or]
      exact reflectedPositiveTimeInverse_le_iff L hL D x c hc hpos ω hω.continuous t s
    · simp [reflectedPositiveTimeInversePath, hω]
  rw [he]
  exact brownianDyadicRegular_measurableSet.compl.union (brownianDyadicRegular_measurableSet.inter
    (measurableSet_le measurable_const
      (reflectedPositiveTimeClock_measurable brownianDyadicPath_jointly_measurable L hL D x c hc s)))

theorem reflectedPositiveTimeInversePath_jointlyMeasurable (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedPositiveTimeInversePath L D x c p.1 p.2) :=
  measurable_uncurry_of_continuous_of_measurable
    (reflectedPositiveTimeInversePath_continuous L hL D x c hc hpos)
    (reflectedPositiveTimeInversePath_measurable L hL D x c hc hpos)

theorem reflectedPositiveTimeInversePath_eq_ae (L D x : ℝ) (c : ℝ → ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t,
      reflectedPositiveTimeInversePath L D x c t ω =
        reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω := by
  filter_upwards [brownianDyadic_regular_ae] with ω hω
  exact fun _ => if_pos hω

theorem reflectedPositiveTimeInversePath_isStoppingTime (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (t : ℝ≥0) :
    IsStoppingTime (positiveTimeChangeCompletedFiltration brownianDyadicPath
      brownianDyadicPath_measurable brownianDyadicMeasure)
      (fun ω => (reflectedPositiveTimeInversePath L D x c t ω : WithTop ℝ≥0)) := by
  intro s
  have hm := reflectedPositiveTimeInverse_isStoppingTime brownianDyadicPath_isBrownianReal
    brownianDyadicPath_measurable L hL D x c hc hpos t s
  have he : {ω | (reflectedPositiveTimeInversePath L D x c t ω : WithTop ℝ≥0) ≤ s}
      =ᵐ[brownianDyadicMeasure] {ω |
        (reflectedPositiveTimeInverse L D x brownianDyadicPath c t ω : WithTop ℝ≥0) ≤ s} := by
    apply eventuallyEq_set.mpr
    filter_upwards [reflectedPositiveTimeInversePath_eq_ae L D x c] with ω hω
    rw [hω t]
  exact EventuallyMeasurableSet.congr hm he

theorem reflectedPositiveTimeInversePath_bound (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (c : ℝ → ℝ) (hc : ContinuousOn c (Icc 0 L)) (hpos : ∀ y ∈ Icc 0 L, 0 < c y)
    (m : ℝ≥0) (hm : 0 < m) (hmc : ∀ y ∈ Icc 0 L, (m : ℝ) ≤ c y)
    (t : ℝ≥0) (ω : ℕ → ℝ) : reflectedPositiveTimeInversePath L D x c t ω ≤ t / m := by
  by_cases hω : BrownianDyadicRegular ω
  · rw [reflectedPositiveTimeInversePath, if_pos hω]
    let v := reflectedPositiveTimeSpeed L hL D x brownianDyadicPath c hc hpos ω hω.continuous
    rw [congrFun (reflectedPositiveTimeInverse_eq L hL D x brownianDyadicPath c hc hpos ω hω.continuous) t]
    obtain ⟨⟨y, hy, he, _⟩, _⟩ :=
      reflectedPositiveTimeSpeed_extrema L hL D x brownianDyadicPath c hc hpos ω hω.continuous
    have hml : m ≤ v.lower := by
      change (m : ℝ) ≤ (v.lower : ℝ)
      rw [← he]
      exact hmc y hy
    exact (v.inverse_bounds t).2.trans (div_le_div_of_nonneg_left (show 0 ≤ t from bot_le) hm hml)
  · simp only [reflectedPositiveTimeInversePath, if_neg hω]
    exact bot_le

end TimeTraps.Probability
