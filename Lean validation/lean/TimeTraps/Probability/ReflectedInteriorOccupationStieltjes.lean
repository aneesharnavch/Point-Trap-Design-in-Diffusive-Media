module

public import TimeTraps.Probability.ReflectedInteriorLocalTimeStieltjes

@[expose] public section

/-! The actual interior occupation time measure is the positive scalar
multiple sigma^{-2} of the proved correction time measure. Its Stieltjes
increments agree with the actual periodized occupation coefficient.
All support assertions here concern a fixed interior level. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def reflectedInteriorOccupationStieltjes (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) (ω : ℕ → ℝ) : StieltjesFunction ℝ :=
  Real.toNNReal (1 / σ ^ 2) • reflectedInteriorStieltjes x hσ hL a ω

def reflectedInteriorOccupationTimeMeasure (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) (ω : ℕ → ℝ) : Measure ℝ :=
  ENNReal.ofReal (1 / σ ^ 2) • reflectedInteriorTimeMeasure x hσ hL a ω

theorem reflectedInteriorOccupationTimeMeasure_eq_stieltjes (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) (ω : ℕ → ℝ) :
    reflectedInteriorOccupationTimeMeasure x hσ hL a ω =
      (reflectedInteriorOccupationStieltjes x hσ hL a ω).measure := by
  rw [reflectedInteriorOccupationStieltjes, StieltjesFunction.measure_smul]
  change (Real.toNNReal (1 / σ ^ 2) : ℝ≥0∞) • (reflectedInteriorStieltjes x hσ hL a ω).measure =
    Real.toNNReal (1 / σ ^ 2) • (reflectedInteriorStieltjes x hσ hL a ω).measure
  rw [Measure.coe_nnreal_smul]

theorem reflectedInteriorOccupationStieltjes_apply {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω)
    (t : ℝ) :
    reflectedInteriorOccupationStieltjes x hσ hL a ω t =
      reflectedInteriorOccupationCoefficient x σ L a t.toNNReal ω := by
  change (Real.toNNReal (1 / σ ^ 2) : ℝ) * reflectedInteriorStieltjes x hσ hL a ω t = _
  rw [Real.coe_toNNReal (1 / σ ^ 2) (div_nonneg zero_le_one (sq_nonneg σ)),
    reflectedInteriorStieltjes_apply hσ hL hω t]
  unfold reflectedInteriorOccupationCoefficient
  ring

theorem reflectedInteriorOccupationStieltjes_apply_nnreal {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω)
    (t : ℝ≥0) :
    reflectedInteriorOccupationStieltjes x hσ hL a ω t.val =
      reflectedInteriorOccupationCoefficient x σ L a t ω := by
  exact (reflectedInteriorOccupationStieltjes_apply hσ hL hω t.val).trans
    (congrArg (fun q => reflectedInteriorOccupationCoefficient x σ L a q ω) (Real.toNNReal_coe (r := t)))

theorem reflectedInteriorOccupationStieltjes_zero {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω) :
    reflectedInteriorOccupationStieltjes x hσ hL a ω 0 = 0 := by
  have he := reflectedInteriorOccupationStieltjes_apply_nnreal hσ hL hω 0
  change reflectedInteriorOccupationStieltjes x hσ hL a ω 0 = _ at he
  rw [he, reflectedInteriorOccupationCoefficient, reflectedInteriorCorrection_zero hσ hω, zero_div]

theorem reflectedInteriorOccupationTimeMeasure_Ioc {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (hω : reflectedInteriorLocalTimeRegular x σ L a ω)
    (S T : ℝ) :
    reflectedInteriorOccupationTimeMeasure x hσ hL a ω (Ioc S T) =
      ENNReal.ofReal (reflectedInteriorOccupationCoefficient x σ L a T.toNNReal ω -
        reflectedInteriorOccupationCoefficient x σ L a S.toNNReal ω) := by
  calc
    _ = ENNReal.ofReal (reflectedInteriorOccupationStieltjes x hσ hL a ω T -
        reflectedInteriorOccupationStieltjes x hσ hL a ω S) := by
      rw [reflectedInteriorOccupationTimeMeasure_eq_stieltjes, StieltjesFunction.measure_Ioc]
    _ = _ := congrArg ENNReal.ofReal (congrArg₂ (fun u v : ℝ => u - v)
      (reflectedInteriorOccupationStieltjes_apply hσ hL hω T)
      (reflectedInteriorOccupationStieltjes_apply hσ hL hω S))

theorem reflectedInteriorOccupationTimeMeasure_singleton (x : ℝ) {σ L : ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (a : ℝ) (ω : ℕ → ℝ) (t : ℝ) :
    reflectedInteriorOccupationTimeMeasure x hσ hL a ω {t} = 0 := by
  rw [reflectedInteriorOccupationTimeMeasure, Measure.smul_apply,
    reflectedInteriorTimeMeasure_singleton x hσ hL a ω t, smul_zero]

theorem reflectedInteriorOccupationTimeMeasure_support {x σ L a : ℝ} {ω : ℕ → ℝ}
    (hσ : 0 < σ) (hL : 0 < L) (ha : a ∈ Ioo 0 L)
    (hω : reflectedInteriorLocalTimeRegular x σ L a ω) :
    (reflectedInteriorOccupationTimeMeasure x hσ hL a ω).support ⊆
      {t : ℝ | 0 ≤ t ∧ reflectedFold L (affineBrownianInput x σ t.toNNReal ω) = a} := by
  have hs : (reflectedInteriorOccupationTimeMeasure x hσ hL a ω).support ⊆
      (reflectedInteriorTimeMeasure x hσ hL a ω).support :=
    Measure.AbsolutelyContinuous.support_mono Measure.smul_absolutelyContinuous
  exact hs.trans (reflectedInteriorTimeMeasure_support hσ hL ⟨ha.1.le, ha.2.le⟩ hω)

end TimeTraps.Probability

end
