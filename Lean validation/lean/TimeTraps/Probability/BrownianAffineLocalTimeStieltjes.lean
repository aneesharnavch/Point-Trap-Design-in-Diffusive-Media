module

public import TimeTraps.Probability.BrownianAffineLocalTimeSupport

@[expose] public section

/-! Actual Stieltjes functions and measures for both affine local-time
normalizations. They agree with the time field on its explicit support
event, extend by zero to negative times, and have the corresponding exact
increments. The two time measures differ by sigma squared. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal Topology

def affineBrownianOccupationStieltjes (x σ a : ℝ) (ω : ℕ → ℝ) : StieltjesFunction ℝ :=
  (Real.toNNReal σ)⁻¹ • brownianLocalTimeStieltjes ((a - x) / σ) ω

def affineBrownianTanakaStieltjes (x σ a : ℝ) (ω : ℕ → ℝ) : StieltjesFunction ℝ :=
  (Real.toNNReal σ) • brownianLocalTimeStieltjes ((a - x) / σ) ω

def affineBrownianOccupationTimeMeasure (x σ a : ℝ) (ω : ℕ → ℝ) : Measure ℝ :=
  (affineBrownianOccupationStieltjes x σ a ω).measure

def affineBrownianTanakaTimeMeasure (x σ a : ℝ) (ω : ℕ → ℝ) : Measure ℝ :=
  (affineBrownianTanakaStieltjes x σ a ω).measure

theorem affineBrownianStieltjes_apply {x σ a : ℝ} {ω : ℕ → ℝ} (hσ : 0 < σ)
    (hω : affineBrownianLocalTimeRegular x σ a ω) (t : ℝ) :
    affineBrownianOccupationStieltjes x σ a ω t =
        affineBrownianOccupationDensity x σ a t.toNNReal ω ∧
      affineBrownianTanakaStieltjes x σ a ω t =
        affineBrownianTanakaCorrection x σ a t.toNNReal ω := by
  rw [(affineBrownianLocalTimeRegular_values hω t.toNNReal).1,
    (affineBrownianLocalTimeRegular_values hω t.toNNReal).2]
  change ((Real.toNNReal σ)⁻¹ : ℝ≥0) * brownianLocalTimeGlobalPath _ _ _ = _ ∧
    (Real.toNNReal σ : ℝ) * brownianLocalTimeGlobalPath _ _ _ = _
  simp only [NNReal.coe_inv, Real.coe_toNNReal σ hσ.le, and_self]

theorem affineBrownianStieltjes_nonpos (x σ a : ℝ) (ω : ℕ → ℝ) {t : ℝ} (ht : t ≤ 0) :
    affineBrownianOccupationStieltjes x σ a ω t = 0 ∧
      affineBrownianTanakaStieltjes x σ a ω t = 0 := by
  change ((Real.toNNReal σ)⁻¹ : ℝ≥0) * brownianLocalTimeRealPath _ t ω = 0 ∧
    (Real.toNNReal σ : ℝ) * brownianLocalTimeRealPath _ t ω = 0
  rw [brownianLocalTimeRealPath_of_nonpos _ ht]
  simp only [mul_zero, and_self]

theorem affineBrownianTimeMeasure_smul (x σ a : ℝ) (ω : ℕ → ℝ) :
    affineBrownianOccupationTimeMeasure x σ a ω =
        (Real.toNNReal σ)⁻¹ • brownianLocalTimeMeasure ((a - x) / σ) ω ∧
      affineBrownianTanakaTimeMeasure x σ a ω =
        (Real.toNNReal σ) • brownianLocalTimeMeasure ((a - x) / σ) ω := by
  exact ⟨StieltjesFunction.measure_smul _ _, StieltjesFunction.measure_smul _ _⟩

theorem affineBrownianTimeMeasure_normalization (x : ℝ) {σ : ℝ} (hσ : 0 < σ)
    (a : ℝ) (ω : ℕ → ℝ) :
    affineBrownianTanakaTimeMeasure x σ a ω =
      ENNReal.ofReal (σ ^ 2) • affineBrownianOccupationTimeMeasure x σ a ω := by
  have hs : Real.toNNReal σ ≠ 0 := ne_of_gt (Real.toNNReal_pos.mpr hσ)
  have hf : affineBrownianTanakaStieltjes x σ a ω =
      (Real.toNNReal σ) ^ 2 • affineBrownianOccupationStieltjes x σ a ω := by
    unfold affineBrownianTanakaStieltjes affineBrownianOccupationStieltjes
    rw [smul_smul, pow_two, mul_assoc, mul_inv_cancel₀ hs, mul_one]
  change (affineBrownianTanakaStieltjes x σ a ω).measure = _
  rw [hf, StieltjesFunction.measure_smul]
  have he : ENNReal.ofReal (σ ^ 2) = ((Real.toNNReal σ) ^ 2 : ℝ≥0) := by
    change (Real.toNNReal (σ ^ 2) : ℝ≥0∞) = _
    rw [Real.toNNReal_pow hσ.le]
  rw [he, Measure.coe_nnreal_smul]
  rfl

theorem affineBrownianTimeMeasure_Ioc {x σ a : ℝ} {ω : ℕ → ℝ} (hσ : 0 < σ)
    (hω : affineBrownianLocalTimeRegular x σ a ω) (S T : ℝ) :
    affineBrownianOccupationTimeMeasure x σ a ω (Ioc S T) =
        ENNReal.ofReal (affineBrownianOccupationDensity x σ a T.toNNReal ω -
          affineBrownianOccupationDensity x σ a S.toNNReal ω) ∧
      affineBrownianTanakaTimeMeasure x σ a ω (Ioc S T) =
        ENNReal.ofReal (affineBrownianTanakaCorrection x σ a T.toNNReal ω -
          affineBrownianTanakaCorrection x σ a S.toNNReal ω) := by
  simp only [affineBrownianOccupationTimeMeasure, affineBrownianTanakaTimeMeasure,
    StieltjesFunction.measure_Ioc, (affineBrownianStieltjes_apply hσ hω S).1,
    (affineBrownianStieltjes_apply hσ hω T).1, (affineBrownianStieltjes_apply hσ hω S).2,
    (affineBrownianStieltjes_apply hσ hω T).2, and_self]

theorem affineBrownianTimeMeasure_singleton (x σ a : ℝ) (ω : ℕ → ℝ) (t : ℝ) :
    affineBrownianOccupationTimeMeasure x σ a ω {t} = 0 ∧
      affineBrownianTanakaTimeMeasure x σ a ω {t} = 0 := by
  rw [(affineBrownianTimeMeasure_smul x σ a ω).1,
    (affineBrownianTimeMeasure_smul x σ a ω).2]
  simp only [Measure.smul_apply, brownianLocalTimeMeasure_singleton, smul_zero, and_self]

theorem affineBrownianTimeMeasure_support {x σ a : ℝ} {ω : ℕ → ℝ} (hσ : 0 < σ)
    (hω : affineBrownianLocalTimeRegular x σ a ω) :
    (affineBrownianOccupationTimeMeasure x σ a ω).support ⊆
        {t : ℝ | 0 ≤ t ∧ affineBrownianInput x σ t.toNNReal ω = a} ∧
      (affineBrownianTanakaTimeMeasure x σ a ω).support ⊆
        {t : ℝ | 0 ≤ t ∧ affineBrownianInput x σ t.toNNReal ω = a} := by
  have hbase : (brownianLocalTimeMeasure ((a - x) / σ) ω).support ⊆
      {t : ℝ | 0 ≤ t ∧ affineBrownianInput x σ t.toNNReal ω = a} := by
    intro t ht
    have hb := brownianLocalTimeMeasure_support hω.2 ht
    exact ⟨hb.1, (affineBrownianInput_eq_level_iff x hσ a t.toNNReal ω).mpr hb.2⟩
  rw [(affineBrownianTimeMeasure_smul x σ a ω).1,
    (affineBrownianTimeMeasure_smul x σ a ω).2]
  exact ⟨(Measure.AbsolutelyContinuous.rfl.smul_left _).support_mono.trans hbase,
    (Measure.AbsolutelyContinuous.rfl.smul_left _).support_mono.trans hbase⟩

end TimeTraps.Probability

end
