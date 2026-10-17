module

public import TimeTraps.Probability.ReflectedInteriorOccupationMoments
public import TimeTraps.Probability.ReflectedInteriorLocalTimeRegularity
public import TimeTraps.Probability.ReflectedFoldOccupationTests
public import Mathlib.Topology.Algebra.InfiniteSum.ENNReal

@[expose] public section

/-! The actual periodized correction divided by the physical variance
equals the established occupation density at each fixed interior level.
The event is chosen per level and works for all times. The existing density
is zero at the endpoints, so the equality deliberately uses an open interval. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem affineBrownianLowerOccupation_sum (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (L : ℝ) (t : ℝ≥0) (ω : ℕ → ℝ) :
    (∑' k : ℤ, affineBrownianOccupationDensity x σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω) =
      affineBrownianLowerRegulator x σ L t ω / σ ^ 2 := by
  simp_rw [affineBrownianOccupationDensity_eq_correction x hσ]
  rw [tsum_div_const]
  rfl

theorem affineBrownianLowerOccupation_summable {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (t : ℝ≥0) :
    Summable (fun k : ℤ => affineBrownianOccupationDensity x σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω) := by
  obtain ⟨K, hz, _⟩ := affineBrownianRegulator_finite_horizon hσ hL hω 0 t
  have hzero (k : ℤ) (hk : k ∉ K) :
      affineBrownianOccupationDensity x σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω = 0 := by
    rw [affineBrownianOccupationDensity_eq_correction x hσ,
      hz k hk t ⟨zero_le, le_rfl⟩, zero_div]
  have hf : (fun k : ℤ => affineBrownianOccupationDensity x σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω).HasFiniteSupport :=
    K.finite_toSet.subset (fun k hk => by
      by_contra hn
      exact hk (hzero k hn))
  exact summable_of_hasFiniteSupport hf

theorem affineBrownianLowerOccupation_ofReal_sum {x σ L : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : affineBrownianLatticeRegular x σ L ω) (t : ℝ≥0) :
    (∑' k : ℤ, ENNReal.ofReal (affineBrownianOccupationDensity x σ
      (((2 * k + 0 : ℤ) : ℝ) * L) t ω)) =
      ENNReal.ofReal (affineBrownianLowerRegulator x σ L t ω / σ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => affineBrownianOccupationDensity_nonneg x hσ _ t ω)
    (affineBrownianLowerOccupation_summable hσ hL hω t), affineBrownianLowerOccupation_sum x hσ]

theorem reflectedInteriorOccupationCoefficient_eq_density {L D x a : ℝ} {ω : ℕ → ℝ}
    (hL : 0 < L) (hD : 0 < D) (ha : a ∈ Ioo 0 L)
    (hω : reflectedInteriorLocalTimeRegular x (Real.sqrt (2 * D)) L a ω) (t : ℝ≥0) :
    reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t ω =
      foldedOccupationDensity L D x t ω a := by
  let σ := Real.sqrt (2 * D)
  have hσ : 0 < σ := Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)
  have hleft (k : ℤ) :
      affineBrownianOccupationDensity x σ (a + (k : ℝ) * (2 * L)) t ω =
        affineBrownianOccupationDensity (x - a) σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω := by
    have he : (a + (k : ℝ) * (2 * L) - x) / σ =
        ((((2 * k + 0 : ℤ) : ℝ) * L) - (x - a)) / σ := by
      push_cast
      ring
    exact congrArg (fun z => σ⁻¹ * brownianLocalTimeTimeField z t ω) he
  have hright (k : ℤ) :
      affineBrownianOccupationDensity x σ ((k : ℝ) * (2 * L) - a) t ω =
        affineBrownianOccupationDensity (x + a) σ (((2 * k + 0 : ℤ) : ℝ) * L) t ω := by
    have he : ((k : ℝ) * (2 * L) - a - x) / σ =
        ((((2 * k + 0 : ℤ) : ℝ) * L) - (x + a)) / σ := by
      push_cast
      ring
    exact congrArg (fun z => σ⁻¹ * brownianLocalTimeTimeField z t ω) he
  have h0 : 0 ≤ affineBrownianLowerRegulator (x - a) σ L t ω / σ ^ 2 :=
    div_nonneg (affineBrownianRegulator_nonneg (x - a) hσ L 0 t ω) (sq_nonneg σ)
  have h1 : 0 ≤ affineBrownianLowerRegulator (x + a) σ L t ω / σ ^ 2 :=
    div_nonneg (affineBrownianRegulator_nonneg (x + a) hσ L 0 t ω) (sq_nonneg σ)
  have he : reflectedFoldDensity L (fun y => ENNReal.ofReal (affineBrownianOccupationDensity x σ y t ω)) a =
      ENNReal.ofReal (affineBrownianLowerRegulator (x - a) σ L t ω / σ ^ 2 +
        affineBrownianLowerRegulator (x + a) σ L t ω / σ ^ 2) := by
    unfold reflectedFoldDensity
    rw [ENNReal.tsum_add]
    simp_rw [hleft, hright]
    rw [affineBrownianLowerOccupation_ofReal_sum hσ hL hω.1 t,
      affineBrownianLowerOccupation_ofReal_sum hσ hL hω.2 t]
    exact (ENNReal.ofReal_add h0 h1).symm
  change (affineBrownianLowerRegulator (x - a) σ L t ω +
      affineBrownianLowerRegulator (x + a) σ L t ω) / σ ^ 2 =
    ((Ioo 0 L).indicator (reflectedFoldDensity L (fun y =>
      ENNReal.ofReal (affineBrownianOccupationDensity x σ y t ω))) a).toReal
  rw [Set.indicator_of_mem ha, he, ENNReal.toReal_ofReal (add_nonneg h0 h1), add_div]

theorem reflectedInteriorOccupationCoefficient_density_all_times_ae (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (ha : a ∈ Ioo 0 L) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0,
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t ω =
        foldedOccupationDensity L D x t ω a := by
  filter_upwards [reflectedInteriorLocalTimeRegular_ae x (Real.sqrt (2 * D)) L a] with ω hω
  exact fun t => reflectedInteriorOccupationCoefficient_eq_density hL hD ha hω t

theorem foldedOccupationDensity_level_memLp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x a : ℝ) (ha : a ∈ Ioo 0 L) (T : ℝ≥0) :
    MemLp (fun ω => foldedOccupationDensity L D x T ω a) 2 brownianDyadicMeasure :=
  (reflectedInteriorOccupationCoefficient_memLp L hL D hD x a T).ae_eq
    ((reflectedInteriorOccupationCoefficient_density_all_times_ae L hL D hD x a ha).mono
      (fun _ hω => hω T))

end TimeTraps.Probability

end
