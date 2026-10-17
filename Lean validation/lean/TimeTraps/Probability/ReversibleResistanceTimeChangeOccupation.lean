module

public import TimeTraps.Probability.ReversibleResistanceTimeChangeOccupationData

@[expose] public section

/-! Actual occupation of the resistance/time-change path. One event
works for all horizons and all bounded Borel tests. The random inverse
horizon is evaluated only in the proved all-time reference occupation
identity. The physical density is rho(z) times the transported local time. -/

namespace TimeTraps.Probability

open Set MeasureTheory Filter TimeTraps.Analysis TimeTraps.Interval
open scoped NNReal

theorem foldedOccupationDensity_weighted_interval (L : ℝ) (hL : 0 < L)
    (D x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) (q : ℝ → ℝ) :
    (∫ y, q y * foldedOccupationDensity L D x T ω y) =
      ∫ y in (0 : ℝ)..L, q y * foldedOccupationDensity L D x T ω y := by
  have he : (fun y => q y * foldedOccupationDensity L D x T ω y) =
      (Ioo 0 L).indicator (fun y => q y * foldedOccupationDensity L D x T ω y) := by
    funext y
    by_cases hy : y ∈ Ioo 0 L
    · rw [indicator_of_mem hy]
    · simp only [indicator_of_notMem hy, foldedOccupationDensity,
        foldedOccupationDensityENNReal, ENNReal.toReal_zero, mul_zero]
  calc
    _ = ∫ y, (Ioo 0 L).indicator (fun y => q y * foldedOccupationDensity L D x T ω y) y :=
      congrArg (fun f : ℝ → ℝ => ∫ y, f y) he
    _ = ∫ y in Ioo 0 L, q y * foldedOccupationDensity L D x T ω y :=
      integral_indicator measurableSet_Ioo
    _ = _ := by rw [intervalIntegral.integral_of_le hL.le, integral_Ioc_eq_integral_Ioo]

theorem reversibleResistanceOccupationDensity_integral_transport
    (A : IntervalMedium) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) (g : ℝ → ℝ) :
    (∫ z, g z * reversibleResistanceOccupationDensity A x T ω z) =
      ∫ y, g (A.resistanceInverse y) * A.resistanceSpeed y *
        foldedOccupationDensity A.resistanceLength 1 (A.resistance x)
          (reversibleResistanceInversePath A x T ω) ω y := by
  let w : ℝ → ℝ := foldedOccupationDensity A.resistanceLength 1 (A.resistance x)
    (reversibleResistanceInversePath A x T ω) ω
  have he : (fun z => g z * reversibleResistanceOccupationDensity A x T ω z) =
      (Ioo A.source.left A.source.right).indicator
        (fun z => g z * A.source.density z * w (A.resistance z)) := by
    funext z
    by_cases hz : z ∈ Ioo A.source.left A.source.right
    · simp only [reversibleResistanceOccupationDensity, indicator_of_mem hz]
      exact (mul_assoc _ _ _).symm
    · simp only [reversibleResistanceOccupationDensity, indicator_of_notMem hz, mul_zero]
  rw [he, integral_indicator measurableSet_Ioo,
    ← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le A.source.increasing.le,
    A.resistance_density_transport g w]
  exact (foldedOccupationDensity_weighted_interval A.resistanceLength A.resistanceLength_pos
    1 (A.resistance x) (reversibleResistanceInversePath A x T ω) ω
      (fun y => g (A.resistanceInverse y) * A.resistanceSpeed y)).symm

theorem reversibleResistanceOccupationDensity_bounded_occupation (A : IntervalMedium) (x : ℝ) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ (g : ℝ → ℝ), Measurable g →
      ∀ M : ℝ, (∀ z, |g z| ≤ M) → ∀ T : ℝ≥0,
        Integrable (fun z => g z * reversibleResistanceOccupationDensity A x T ω z) volume ∧
          IntervalIntegrable (fun t => g (reversibleResistancePath A x t.toNNReal ω)) volume 0 T.val ∧
          (∫ z, g z * reversibleResistanceOccupationDensity A x T ω z) =
            ∫ t in (0 : ℝ)..T.val, g (reversibleResistancePath A x t.toNNReal ω) := by
  filter_upwards [reversibleResistanceReference_weighted_occupation A x] with ω hω
  intro g hg M hb T
  have hi := hω g hg M hb T
  let w : ℝ → ℝ := foldedOccupationDensity A.resistanceLength 1 (A.resistance x)
    (reversibleResistanceInversePath A x T ω) ω
  have hy : IntervalIntegrable
      (fun y => g (A.resistanceInverse y) * A.resistanceSpeed y * w y)
        volume 0 A.resistanceLength :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le A.resistanceLength_pos.le).mpr hi.1.integrableOn
  have hz := (A.resistance_density_integrable_iff g w).mpr hy
  have he : (fun z => g z * reversibleResistanceOccupationDensity A x T ω z) =
      (Ioo A.source.left A.source.right).indicator
        (fun z => g z * A.source.density z * w (A.resistance z)) := by
    funext z
    by_cases hz : z ∈ Ioo A.source.left A.source.right
    · simp only [reversibleResistanceOccupationDensity, indicator_of_mem hz]
      exact (mul_assoc _ _ _).symm
    · simp only [reversibleResistanceOccupationDensity, indicator_of_notMem hz, mul_zero]
  refine ⟨?_, ?_, (reversibleResistanceOccupationDensity_integral_transport A x T ω g).trans hi.2⟩
  · rw [he, integrable_indicator_iff measurableSet_Ioo]
    exact (intervalIntegrable_iff_integrableOn_Ioo_of_le A.source.increasing.le).mp hz
  · exact brownianItoDrift_bounded_intervalIntegrable hg
      (reversibleResistancePath_jointlyMeasurable A x) hb T ω

end TimeTraps.Probability
