module

public import TimeTraps.Probability.DyadicWeightedIncrementStieltjes
public import TimeTraps.Probability.ReflectedInteriorOccupationStieltjes
public import TimeTraps.Probability.ReflectedRegulatorIntegral

@[expose] public section

/-! Weighted increments of the actual correction, normalized occupation,
and regulator paths converge to their actual Stieltjes integrals on the
already proved regular events. No new version or normalization is used. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal Topology

theorem dyadicWeightedIncrement_reflectedInteriorCorrection_tendsto
    {x σ L a : ℝ} {ω : ℕ → ℝ} (hσ : 0 < σ) (hL : 0 < L)
    (hω : reflectedInteriorLocalTimeRegular x σ L a ω)
    (H : ℝ≥0 → ℝ) (hH : Continuous H) (T : ℝ≥0) :
    Tendsto (dyadicWeightedIncrement H (fun t => reflectedInteriorCorrection x σ L a t ω) T)
      atTop (𝓝 (∫ r in Ioc (0 : ℝ) T.val, H r.toNNReal
        ∂(reflectedInteriorStieltjes x hσ hL a ω).measure)) := by
  have he : (fun t : ℝ≥0 => reflectedInteriorStieltjes x hσ hL a ω t.val) =
      fun t => reflectedInteriorCorrection x σ L a t ω := by
    funext t
    exact (reflectedInteriorStieltjes_apply hσ hL hω t.val).trans
      (congrArg (fun u => reflectedInteriorCorrection x σ L a u ω) (Real.toNNReal_coe (r := t)))
  have h := dyadicWeightedIncrement_stieltjes_tendsto (reflectedInteriorStieltjes x hσ hL a ω) H hH T
  rw [he] at h
  exact h

theorem dyadicWeightedIncrement_reflectedInteriorOccupation_tendsto
    {x σ L a : ℝ} {ω : ℕ → ℝ} (hσ : 0 < σ) (hL : 0 < L)
    (hω : reflectedInteriorLocalTimeRegular x σ L a ω)
    (H : ℝ≥0 → ℝ) (hH : Continuous H) (T : ℝ≥0) :
    Tendsto (dyadicWeightedIncrement H
      (fun t => reflectedInteriorOccupationCoefficient x σ L a t ω) T) atTop
      (𝓝 (∫ r in Ioc (0 : ℝ) T.val, H r.toNNReal
        ∂reflectedInteriorOccupationTimeMeasure x hσ hL a ω)) := by
  have he : (fun t : ℝ≥0 => reflectedInteriorOccupationStieltjes x hσ hL a ω t.val) =
      fun t => reflectedInteriorOccupationCoefficient x σ L a t ω :=
    funext (reflectedInteriorOccupationStieltjes_apply_nnreal hσ hL hω)
  have h := dyadicWeightedIncrement_stieltjes_tendsto
    (reflectedInteriorOccupationStieltjes x hσ hL a ω) H hH T
  rw [he] at h
  rw [reflectedInteriorOccupationTimeMeasure_eq_stieltjes]
  exact h

theorem dyadicWeightedIncrement_affineBrownianRegulator_tendsto
    {x σ L : ℝ} {ω : ℕ → ℝ} (hσ : 0 < σ) (hL : 0 < L)
    (hω : affineBrownianLatticeRegular x σ L ω) (b : ℤ)
    (H : ℝ≥0 → ℝ) (hH : Continuous H) (T : ℝ≥0) :
    Tendsto (dyadicWeightedIncrement H (fun t => affineBrownianRegulator x σ L b t ω) T)
      atTop (𝓝 (∫ r in Ioc (0 : ℝ) T.val, H r.toNNReal
        ∂(affineBrownianRegulatorStieltjes x hσ hL b ω).measure)) := by
  have he : (fun t : ℝ≥0 => affineBrownianRegulatorStieltjes x hσ hL b ω t.val) =
      fun t => affineBrownianRegulator x σ L b t ω :=
    funext (affineBrownianRegulatorStieltjes_apply_nnreal hσ hL hω b)
  have h := dyadicWeightedIncrement_stieltjes_tendsto
    (affineBrownianRegulatorStieltjes x hσ hL b ω) H hH T
  rw [he] at h
  exact h

end TimeTraps.Probability
