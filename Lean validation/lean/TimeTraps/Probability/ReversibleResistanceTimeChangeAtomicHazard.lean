module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeLocalTimeContact
public import TimeTraps.Probability.ReflectedAtomicHazardPaths

@[expose] public section

/-! Finite physical atomic killing, constructed from the transported
occupation local times with the original strengths. The exact reference
hazard identity has no missing conductance or speed-density factor. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal

variable {ι : Type*} [Fintype ι]

noncomputable def reversibleResistanceAtomicHazard (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  ∑ i, κ i * reversibleResistanceLocalTime A x (a i) T ω

noncomputable def reversibleResistanceAtomicSurvival (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  Real.exp (-reversibleResistanceAtomicHazard A x a κ T ω)

theorem reversibleResistanceAtomicHazard_reference (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    reversibleResistanceAtomicHazard A x a κ T ω =
      reflectedAtomicHazard A.resistanceLength 1 (A.resistance x)
        (fun i => A.resistance (a i)) κ (reversibleResistanceInversePath A x T ω) ω := rfl

theorem reversibleResistanceAtomicSurvival_reference (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    reversibleResistanceAtomicSurvival A x a κ T ω =
      reflectedAtomicSurvival A.resistanceLength 1 (A.resistance x)
        (fun i => A.resistance (a i)) κ (reversibleResistanceInversePath A x T ω) ω := rfl

theorem reversibleResistanceAtomicHazard_jointlyMeasurable (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reversibleResistanceAtomicHazard A x a κ p.1 p.2) := by
  unfold reversibleResistanceAtomicHazard
  exact Finset.measurable_sum Finset.univ (fun i _ =>
    measurable_const.mul (reversibleResistanceLocalTime_jointlyMeasurable A x (a i)))

theorem reversibleResistanceAtomicSurvival_jointlyMeasurable (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reversibleResistanceAtomicSurvival A x a κ p.1 p.2) :=
  (reversibleResistanceAtomicHazard_jointlyMeasurable A x a κ).neg.exp

theorem reversibleResistanceAtomicHazard_nonneg (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (ω : ℕ → ℝ) :
    0 ≤ reversibleResistanceAtomicHazard A x a κ T ω :=
  Finset.sum_nonneg (fun i _ => mul_nonneg (hκ i)
    (reversibleResistanceLocalTime_nonneg A x (a i) T ω))

theorem reversibleResistanceAtomicSurvival_bounds (A : IntervalMedium) (x : ℝ)
    (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (ω : ℕ → ℝ) :
    0 < reversibleResistanceAtomicSurvival A x a κ T ω ∧
      reversibleResistanceAtomicSurvival A x a κ T ω ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (reversibleResistanceAtomicHazard_nonneg A x a κ hκ T ω))⟩

end TimeTraps.Probability
