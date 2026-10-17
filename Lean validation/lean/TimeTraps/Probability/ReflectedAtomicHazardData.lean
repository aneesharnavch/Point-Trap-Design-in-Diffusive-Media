module

public import TimeTraps.Probability.ReflectedInteriorOccupationMeasurable
public import TimeTraps.Probability.ExponentialKillingContact

@[expose] public section

/-! The actual finite atomic hazard and exponential survival weight,
built from the proved interior occupation coefficients. Their elementary
measurability and positivity properties hold for the literal versions.
The occupation interpretation of the sites is restricted to (0,L). -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι]

def reflectedAtomicHazard (L D x : ℝ) (a κ : ι → ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  weightedContactHazard κ
    (fun i => reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) t) ω

def reflectedAtomicSurvival (L D x : ℝ) (a κ : ι → ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  Real.exp (-reflectedAtomicHazard L D x a κ t ω)

theorem affineBrownianRegulator_time_jointlyMeasurable (x σ L : ℝ) (b : ℤ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => affineBrownianRegulator x σ L b p.1 p.2) := by
  unfold affineBrownianRegulator
  apply Measurable.tsum
  intro k
  have hφ : Measurable (fun p : ℝ≥0 × (ℕ → ℝ) =>
      ((((((2 * k + b : ℤ) : ℝ) * L) - x) / σ, p.1), p.2)) := by fun_prop
  have hm := brownianLocalTimeTimeField_jointlyMeasurable.comp hφ
  exact measurable_const.mul hm

theorem reflectedInteriorOccupationCoefficient_time_jointlyMeasurable (x σ L a : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) =>
      reflectedInteriorOccupationCoefficient x σ L a p.1 p.2) :=
  ((affineBrownianRegulator_time_jointlyMeasurable (x - a) σ L 0).add
    (affineBrownianRegulator_time_jointlyMeasurable (x + a) σ L 0)).div_const (σ ^ 2)

theorem reflectedAtomicHazard_jointlyMeasurable (L D x : ℝ) (a κ : ι → ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedAtomicHazard L D x a κ p.1 p.2) := by
  unfold reflectedAtomicHazard weightedContactHazard
  apply Finset.measurable_sum
  intro i _
  exact measurable_const.mul
    (reflectedInteriorOccupationCoefficient_time_jointlyMeasurable x (Real.sqrt (2 * D)) L (a i))

theorem reflectedAtomicSurvival_jointlyMeasurable (L D x : ℝ) (a κ : ι → ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedAtomicSurvival L D x a κ p.1 p.2) :=
  (reflectedAtomicHazard_jointlyMeasurable L D x a κ).neg.exp

theorem reflectedAtomicHazard_nonneg (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ≥0) (ω : ℕ → ℝ) :
    0 ≤ reflectedAtomicHazard L D x a κ t ω :=
  weightedContactHazard_nonneg κ
    (fun i => reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) t)
    hκ (fun i ω => reflectedInteriorOccupationCoefficient_nonneg x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) L (a i) t ω) ω

theorem reflectedAtomicSurvival_bounds (L : ℝ) {D : ℝ} (hD : 0 < D)
    (x : ℝ) (a κ : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i) (t : ℝ≥0) (ω : ℕ → ℝ) :
    0 < reflectedAtomicSurvival L D x a κ t ω ∧ reflectedAtomicSurvival L D x a κ t ω ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (reflectedAtomicHazard_nonneg L hD x a κ hκ t ω))⟩

end TimeTraps.Probability

end
