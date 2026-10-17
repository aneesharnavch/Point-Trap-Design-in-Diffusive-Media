module

public import Mathlib.MeasureTheory.Integral.IntegralEqImproper
public import Mathlib.Topology.Instances.NNReal.Lemmas

@[expose] public section

/-! A finite limit of nonnegative finite-horizon integrals determines the
actual integral on the positive half-line. Integrability is derived by
monotone exhaustion; it is not an additional infinite-horizon premise. -/

namespace TimeTraps.Analysis

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem survivalIntegralLimit {w : ℝ≥0 → ℝ} {C : ℝ}
    (hn : ∀ t, 0 ≤ w t)
    (hi : ∀ T : ℝ≥0, IntervalIntegrable (fun r : ℝ => w r.toNNReal) volume 0 T.val)
    (hl : Tendsto (fun T : ℝ≥0 => ∫ r in (0 : ℝ)..T.val, w r.toNNReal)
      atTop (𝓝 C)) :
    IntegrableOn (fun r : ℝ => w r.toNNReal) (Ioi (0 : ℝ)) ∧
      (∫ r in Ioi (0 : ℝ), w r.toNNReal) = C ∧
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (w r.toNNReal)) = ENNReal.ofReal C := by
  have ht : Tendsto (fun T : ℝ≥0 => T.val) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hfinite : IntegrableOn (fun r : ℝ => w r.toNNReal) (Ioi (0 : ℝ)) := by
    apply integrableOn_Ioi_of_intervalIntegral_norm_tendsto C 0 (fun T => (hi T).1) ht
    simpa only [Real.norm_of_nonneg (hn _)] using hl
  have he : (∫ r in Ioi (0 : ℝ), w r.toNNReal) = C :=
    tendsto_nhds_unique (intervalIntegral_tendsto_integral_Ioi 0 hfinite ht) hl
  refine ⟨hfinite, he, ?_⟩
  rw [← ofReal_integral_eq_lintegral_ofReal hfinite (Eventually.of_forall (fun r => hn r.toNNReal)), he]

theorem survivalIntegralLimit_of_continuous {w : ℝ≥0 → ℝ} {C : ℝ}
    (hn : ∀ t, 0 ≤ w t) (hw : Continuous w)
    (hl : Tendsto (fun T : ℝ≥0 => ∫ r in (0 : ℝ)..T.val, w r.toNNReal)
      atTop (𝓝 C)) :
    IntegrableOn (fun r : ℝ => w r.toNNReal) (Ioi (0 : ℝ)) ∧
      (∫ r in Ioi (0 : ℝ), w r.toNNReal) = C ∧
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (w r.toNNReal)) = ENNReal.ofReal C :=
  survivalIntegralLimit hn (fun _ => (hw.comp continuous_real_toNNReal).intervalIntegrable _ _) hl

theorem survivalIntegralLimit_of_antitone {w : ℝ≥0 → ℝ} {C : ℝ}
    (hn : ∀ t, 0 ≤ w t) (hw : Antitone w)
    (hl : Tendsto (fun T : ℝ≥0 => ∫ r in (0 : ℝ)..T.val, w r.toNNReal)
      atTop (𝓝 C)) :
    IntegrableOn (fun r : ℝ => w r.toNNReal) (Ioi (0 : ℝ)) ∧
      (∫ r in Ioi (0 : ℝ), w r.toNNReal) = C ∧
      (∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (w r.toNNReal)) = ENNReal.ofReal C :=
  survivalIntegralLimit hn (fun _ =>
    (hw.comp_monotone Real.toNNReal_monotone).intervalIntegrable) hl

end TimeTraps.Analysis
