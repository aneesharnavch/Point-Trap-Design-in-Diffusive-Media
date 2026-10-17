module

public import TimeTraps.Probability.ReversibleResistanceLocalTimeRevuzBound
public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimeWeightedContact

@[expose] public section

/-! Literal physical contact integrals used in the Revuz test. The carried
contact measure evaluates every spatial test at the fixed site, with no
extra speed-density or conductance factor. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal ENNReal Topology

noncomputable def reversibleResistanceRevuzContact (A : IntervalMedium) (x a : ℝ)
    (g : ℝ → ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  ∫ t in Ioc (0 : ℝ) T.val, g (reversibleResistancePath A x t.toNNReal ω)
    ∂reversibleResistanceLocalTimeMeasure A x a ω

theorem reversibleResistanceRevuzContact_ae (A : IntervalMedium) (x : ℝ) {a : ℝ}
    (ha : a ∈ Ioo A.source.left A.source.right) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ g : ℝ → ℝ, ∀ T : ℝ≥0,
      reversibleResistanceRevuzContact A x a g T ω = g a * reversibleResistanceLocalTime A x a T ω := by
  filter_upwards [brownianDyadic_regular_ae,
    reflectedInteriorLocalTimeRegular_ae (A.resistance x) (Real.sqrt (2 * 1))
      A.resistanceLength (A.resistance a)] with ω hω hr g T
  have he := (reversibleResistanceLocalTimeMeasure_weighted_contact A x ha hω hr
    (fun _ => (1 : ℝ)) continuous_const g T).2
  simp only [one_mul] at he
  change reversibleResistanceRevuzContact A x a g T ω = _ at he
  rw [he, setIntegral_const, smul_eq_mul, mul_one, Measure.real,
    reversibleResistanceLocalTimeMeasure_mass A x a hω hr T,
    ENNReal.toReal_ofReal (reversibleResistanceLocalTime_nonneg A x a T ω)]

theorem reversibleResistanceRevuzContact_integrable (A : IntervalMedium) (x : ℝ) {a : ℝ}
    (ha : a ∈ Ioo A.source.left A.source.right) (g : ℝ → ℝ) (T : ℝ≥0) :
    Integrable (reversibleResistanceRevuzContact A x a g T) brownianDyadicMeasure := by
  apply (((reversibleResistanceLocalTime_memLp_two A x a T).integrable (by norm_num)).const_mul (g a)).congr
  filter_upwards [reversibleResistanceRevuzContact_ae A x ha] with ω hω
  exact (hω g T).symm

theorem reversibleResistanceRevuzContact_mean (A : IntervalMedium) (x : ℝ) {a : ℝ}
    (ha : a ∈ Ioo A.source.left A.source.right) (g : ℝ → ℝ) (T : ℝ≥0) :
    (∫ ω, reversibleResistanceRevuzContact A x a g T ω ∂brownianDyadicMeasure) =
      g a * ∫ ω, reversibleResistanceLocalTime A x a T ω ∂brownianDyadicMeasure := by
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [reversibleResistanceRevuzContact_ae A x ha] with ω hω
  exact hω g T

end TimeTraps.Probability
