module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzBound

@[expose] public section

/-! Continuity in time of the actual fixed-site local-time expectation.
The dominating reference terminal local time is derived, not assumed. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

theorem reversibleResistanceLocalTime_mean_continuous_compact (A : IntervalMedium) (x a : ℝ) (T : ℝ≥0) :
    Continuous (fun t : BrownianCompactTime T => ∫ ω,
      reversibleResistanceLocalTime A x a t.val ω ∂brownianDyadicMeasure) := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded A x T
  let F : BrownianCompactTime T → (ℕ → ℝ) → ℝ := fun t ω => reversibleResistanceLocalTime A x a t.val ω
  let B := reflectedInteriorOccupationCoefficient (A.resistance x) (Real.sqrt (2 * 1))
    A.resistanceLength (A.resistance a) S
  have hm (t : BrownianCompactTime T) : AEStronglyMeasurable (F t) brownianDyadicMeasure :=
    (reversibleResistanceLocalTime_memLp_two A x a t.val).aestronglyMeasurable
  apply continuous_of_dominated (μ := brownianDyadicMeasure) (F := F) (bound := B) hm
  · intro t
    filter_upwards [reversibleResistanceLocalTime_paths A x a,
      reversibleResistanceLocalTime_le_reference_ae A x a T S hS] with ω hp hb
    change ‖reversibleResistanceLocalTime A x a t.val ω‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (reversibleResistanceLocalTime_nonneg A x a t.val ω)]
    exact (hp.2.1 t.property.2).trans hb
  · exact (reflectedInteriorOccupationCoefficient_memLp A.resistanceLength A.resistanceLength_pos
      1 zero_lt_one (A.resistance x) (A.resistance a) S).integrable (by norm_num)
  · filter_upwards [reversibleResistanceLocalTime_paths A x a] with ω hp
    exact hp.1.comp continuous_subtype_val

theorem reversibleResistanceLocalTime_mean_continuous (A : IntervalMedium) (x a : ℝ) :
    Continuous (fun t : ℝ≥0 => ∫ ω, reversibleResistanceLocalTime A x a t ω ∂brownianDyadicMeasure) := by
  rw [continuous_iff_continuousAt]
  intro t
  have hc : ContinuousOn (fun s : ℝ≥0 => ∫ ω,
      reversibleResistanceLocalTime A x a s ω ∂brownianDyadicMeasure) (Icc 0 (t + 1)) :=
    continuousOn_iff_continuous_domRestrict.mpr (reversibleResistanceLocalTime_mean_continuous_compact A x a (t + 1))
  apply hc.continuousAt
  have he : Icc (0 : ℝ≥0) (t + 1) = Iic (t + 1) := by ext s; simp
  rw [he]
  exact Iic_mem_nhds (by simp : t < t + 1)

end TimeTraps.Probability
