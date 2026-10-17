module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeBandData
public import TimeTraps.Probability.ReflectedLocalTimeBandRandomHorizon

@[expose] public section

/-! Mean-square convergence of actual physical occupation-band functionals
to the fixed-site local time. The inverse horizon bound is derived from
continuous positive speed, with no coefficient differentiability. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal Topology

theorem reversibleResistanceOccupationBand_error_memLp (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) {h : ℝ}
    (hh : 0 < h)
    (hsmall : h < min (A.resistance a / 2) ((A.resistanceLength - A.resistance a) / 2)) :
    MemLp (fun ω => reversibleResistanceOccupationBand A x a h T ω -
      reversibleResistanceLocalTime A x a T ω) 2 brownianDyadicMeasure := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded A x T
  have hm := reflectedOccupationBand_random_error_memLp A.resistanceLength A.resistanceLength_pos
    1 (by norm_num) (A.resistance x) S ⟨A.resistance a, reversibleResistance_site_interior A ha⟩
      hh hsmall (reversibleResistanceInversePath A x T) (reversibleResistanceInversePath_measurable A x T)
        (Eventually.of_forall hS)
  apply MemLp.ae_eq _ hm
  filter_upwards [reversibleResistanceOccupationBand_reference_ae A x] with ω he
  rw [he a h T]
  rfl

theorem reversibleResistanceOccupationBand_square_tendsto (A : IntervalMedium) (x : ℝ)
    {a : ℝ} (ha : a ∈ Ioo A.source.left A.source.right) (T : ℝ≥0) :
    Tendsto (fun h => ∫ ω, (reversibleResistanceOccupationBand A x a h T ω -
      reversibleResistanceLocalTime A x a T ω) ^ 2 ∂brownianDyadicMeasure) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨S, hS⟩ := reversibleResistanceInversePath_bounded A x T
  have ht := reflectedOccupationBand_random_horizon_square_tendsto
    A.resistanceLength A.resistanceLength_pos 1 (by norm_num) (A.resistance x) S
      ⟨A.resistance a, reversibleResistance_site_interior A ha⟩
      (reversibleResistanceInversePath A x T) (reversibleResistanceInversePath_measurable A x T)
        (Eventually.of_forall hS)
  apply ht.congr
  intro h
  apply integral_congr_ae
  filter_upwards [reversibleResistanceOccupationBand_reference_ae A x] with ω he
  rw [he a h T]
  rfl

end TimeTraps.Probability
