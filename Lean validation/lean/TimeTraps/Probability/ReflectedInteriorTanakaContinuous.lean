module

public import TimeTraps.Probability.ReflectedInteriorTanakaFormula
public import TimeTraps.Probability.ReflectedInteriorKinkIntegrandPath
public import TimeTraps.Probability.ReflectedFoldTrajectory

@[expose] public section

/-! Single-interior-kink Tanaka on one event throughout a fixed compact
horizon, using the canonical continuous original-Brownian integral path.
The diffusion version retains the actual boundary and interior corrections. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedInteriorTanaka_continuous_ae (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      |reflectedFold L (affineBrownianInput x σ t ω) - a| - |reflectedFold L x - a| =
        reflectedInteriorKinkHorizonPath L hL a ha x hσ T t ω +
        reflectedInteriorCorrection x σ L a t ω - affineBrownianLowerRegulator x σ L t ω -
          affineBrownianUpperRegulator x σ L t ω := by
  have ht (t : BrownianCompactTime T) :
      ∀ᵐ ω ∂brownianDyadicMeasure,
        |reflectedFold L (affineBrownianInput x σ t.val ω) - a| - |reflectedFold L x - a| =
          reflectedInteriorKinkHorizonPath L hL a ha x hσ T t.val ω +
          reflectedInteriorCorrection x σ L a t.val ω - affineBrownianLowerRegulator x σ L t.val ω -
            affineBrownianUpperRegulator x σ L t.val ω := by
    filter_upwards [reflectedInteriorTanaka_formula L hL a ha x hσ t.val,
      reflectedInteriorKinkHorizonPath_integral_ae L hL a ha x hσ T t.val] with ω hf hi
    rw [min_eq_left t.property.2] at hi
    rw [← hi] at hf
    exact hf
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ n : ℕ,
      |reflectedFold L (affineBrownianInput x σ (denseSeq (BrownianCompactTime T) n).val ω) - a| -
        |reflectedFold L x - a| =
      reflectedInteriorKinkHorizonPath L hL a ha x hσ T (denseSeq (BrownianCompactTime T) n).val ω +
        reflectedInteriorCorrection x σ L a (denseSeq (BrownianCompactTime T) n).val ω -
        affineBrownianLowerRegulator x σ L (denseSeq (BrownianCompactTime T) n).val ω -
        affineBrownianUpperRegulator x σ L (denseSeq (BrownianCompactTime T) n).val ω :=
    ae_all_iff.mpr (fun n => ht (denseSeq (BrownianCompactTime T) n))
  filter_upwards [hall, brownianDyadic_regular_ae, affineBrownianLatticeRegular_ae x σ L,
    reflectedInteriorLocalTimeRegular_ae x σ L a] with ω he hB hK hC
  have hx := (reflectedFold_continuous L).comp (affineBrownianInput_continuous x σ hB)
  have hleft := ((hx.sub (continuous_const (y := a))).abs).sub
    (continuous_const (y := |reflectedFold L x - a|))
  have hright : Continuous (fun t : ℝ≥0 =>
      reflectedInteriorKinkHorizonPath L hL a ha x hσ T t ω +
        reflectedInteriorCorrection x σ L a t ω - affineBrownianLowerRegulator x σ L t ω -
        affineBrownianUpperRegulator x σ L t ω) :=
    (((reflectedInteriorKinkHorizonPath_continuous L hL a ha x hσ T ω).add
      (reflectedInteriorCorrection_continuous hσ hL hC)).sub
      (affineBrownianRegulator_continuous hσ hL hK 0)).sub
      (affineBrownianRegulator_continuous hσ hL hK 1)
  have heq := (denseRange_denseSeq (BrownianCompactTime T)).equalizer
    (hleft.comp continuous_subtype_val) (hright.comp continuous_subtype_val) (funext he)
  exact fun t ht => congrFun heq ⟨t, zero_le, ht⟩

theorem reflectedInteriorTanaka_diffusion_ae (L : ℝ) (hL : 0 < L) (a : ℝ)
    (ha : a ∈ Ioo 0 L) (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂brownianDyadicMeasure, ∀ t : ℝ≥0, t ≤ T →
      |foldedTrajectory L D x brownianDyadicPath t ω - a| - |reflectedFold L x - a| =
        reflectedInteriorKinkHorizonPath L hL a ha x
          (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T t ω +
        (2 * D) * reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t ω -
        affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L t ω -
          affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L t ω := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  filter_upwards [reflectedInteriorTanaka_continuous_ae L hL a ha x hσ T] with ω he
  intro t ht
  have hn := reflectedInteriorOccupationCoefficient_normalization x hσ L a t ω
  rw [Real.sq_sqrt (by positivity : 0 ≤ 2 * D)] at hn
  have h := he t ht
  rw [← hn] at h
  exact h

end TimeTraps.Probability
