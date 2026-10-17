module

public import TimeTraps.Analysis.IntervalSlopeUniquenessRegularity
public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Normed.Operator.Prod

@[expose] public section

/-! The time-dependent linear pair field for a Sturm state and flux.
Continuous coefficients on the original closed interval supply a uniform
Lipschitz constant. No derivatives of the coefficients are used. -/

noncomputable section

namespace TimeTraps.Analysis

open Set MeasureTheory Filter
open scoped Topology NNReal

def intervalLinearPairField (q c : ℝ → ℝ) (x : ℝ) : (ℝ × ℝ) →L[ℝ] (ℝ × ℝ) :=
  (q x • ContinuousLinearMap.snd ℝ ℝ ℝ).prod
    (c x • ContinuousLinearMap.fst ℝ ℝ ℝ)

theorem intervalLinearPairField_apply (q c : ℝ → ℝ) (x : ℝ) (z : ℝ × ℝ) :
    intervalLinearPairField q c x z = (q x * z.2, c x * z.1) := rfl

theorem intervalLinearPairField_lipschitz {q c : ℝ → ℝ} {a b : ℝ}
    (hq : ContinuousOn q (Icc a b)) (hc : ContinuousOn c (Icc a b)) :
    ∃ K : ℝ≥0, ∀ x ∈ Icc a b, LipschitzWith K (intervalLinearPairField q c x) := by
  let Q : C(Icc a b, ℝ) := ⟨fun x => q x.val, hq.domRestrict⟩
  let C : C(Icc a b, ℝ) := ⟨fun x => c x.val, hc.domRestrict⟩
  let K : ℝ≥0 := ⟨‖Q‖ + ‖C‖, add_nonneg (norm_nonneg _) (norm_nonneg _)⟩
  refine ⟨K, fun x hx => (intervalLinearPairField q c x).lipschitz.weaken ?_⟩
  change ‖intervalLinearPairField q c x‖ ≤ ‖Q‖ + ‖C‖
  rw [intervalLinearPairField, ContinuousLinearMap.opNorm_prod, Prod.norm_def]
  apply max_le
  · calc
      _ ≤ ‖q x‖ * ‖ContinuousLinearMap.snd ℝ ℝ ℝ‖ := norm_smul_le _ _
      _ ≤ ‖Q‖ * 1 := mul_le_mul (Q.norm_coe_le_norm ⟨x, hx⟩)
        (ContinuousLinearMap.norm_snd_le ℝ ℝ ℝ) (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖Q‖ + ‖C‖ := by simpa only [mul_one] using le_add_of_nonneg_right (norm_nonneg C)
  · calc
      _ ≤ ‖c x‖ * ‖ContinuousLinearMap.fst ℝ ℝ ℝ‖ := norm_smul_le _ _
      _ ≤ ‖C‖ * 1 := mul_le_mul (C.norm_coe_le_norm ⟨x, hx⟩)
        (ContinuousLinearMap.norm_fst_le ℝ ℝ ℝ) (norm_nonneg _) (norm_nonneg _)
      _ ≤ ‖Q‖ + ‖C‖ := by simpa only [mul_one] using le_add_of_nonneg_left (norm_nonneg Q)

end TimeTraps.Analysis

end
