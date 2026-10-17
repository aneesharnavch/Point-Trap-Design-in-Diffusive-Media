module

public import TimeTraps.Probability.BrownianSequenceContinuity

@[expose] public section

/-! A countable sampling scheme containing both every dense grid time
and an arbitrary countable family of additional observation times. -/

namespace TimeTraps.Probability

open scoped NNReal

noncomputable def denseAugmentedObservationTime (τ : ℕ → ℝ≥0) (i : ℕ) : ℝ≥0 :=
  if (Nat.unpair i).1 = 0 then brownianDyadicTime (Nat.unpair i).2 else τ (Nat.unpair i).2

theorem denseAugmentedObservationTime_grid (τ : ℕ → ℝ≥0) (i : ℕ) :
    denseAugmentedObservationTime τ (Nat.pair 0 i) = brownianDyadicTime i := by
  simp [denseAugmentedObservationTime]

theorem denseAugmentedObservationTime_added (τ : ℕ → ℝ≥0) (i : ℕ) :
    denseAugmentedObservationTime τ (Nat.pair 1 i) = τ i := by
  simp only [denseAugmentedObservationTime, Nat.unpair_pair, if_neg Nat.one_ne_zero]

end TimeTraps.Probability
