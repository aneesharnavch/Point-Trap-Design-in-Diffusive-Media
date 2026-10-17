module

public import TimeTraps.Analysis.ReflectedInteriorTanakaSlopeData
public import TimeTraps.Analysis.ReflectedFoldSlopeRegularity
public import TimeTraps.Probability.BrownianCountableIntegrandCutoff

@[expose] public section

/-! The normalized interior-kink coefficient is the existing canonical
midpoint slope evaluated at affine Brownian input. Its possible scalar
discontinuities lie in the three explicit affine preimage lattices:
fold corners and the positive/negative preimages of the interior level. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

def reflectedInteriorKinkCoefficient (L a x σ b : ℝ) : ℝ :=
  reflectedInteriorTanakaSlope L a (x + σ * b)

def reflectedInteriorKinkExceptional (L a x σ : ℝ) : Set ℝ :=
  range (fun j : ℤ => ((j : ℝ) * L - x) / σ) ∪
    (range (fun k : ℤ => (a + (k : ℝ) * (2 * L) - x) / σ) ∪
      range (fun k : ℤ => (-a + (k : ℝ) * (2 * L) - x) / σ))

theorem reflectedInteriorKinkCoefficient_measurable (L : ℝ) (hL : 0 < L) (a x σ : ℝ) :
    Measurable (reflectedInteriorKinkCoefficient L a x σ) := by
  have hi : Measurable (fun b : ℝ => x + σ * b) :=
    measurable_const.add (measurable_const.mul measurable_id)
  exact (brownianSign_measurable.comp
    (((reflectedFold_continuous L).measurable.comp hi).sub_const a)).mul
    ((reflectedFoldSlope_measurable L hL).comp hi)

theorem reflectedInteriorKinkCoefficient_bound (L : ℝ) (hL : 0 < L) (a x σ b : ℝ) :
    |reflectedInteriorKinkCoefficient L a x σ b| ≤ 1 := by
  unfold reflectedInteriorKinkCoefficient reflectedInteriorTanakaSlope
  rw [abs_mul]
  exact (mul_le_mul (brownianSign_abs_le _) (reflectedFoldSlope_bound L hL _)
    (abs_nonneg _) zero_le_one).trans_eq (mul_one 1)

theorem reflectedInteriorKinkExceptional_countable (L a x σ : ℝ) :
    (reflectedInteriorKinkExceptional L a x σ).Countable :=
  (countable_range _).union ((countable_range _).union (countable_range _))

theorem reflectedInteriorKinkCoefficient_continuousAt (L : ℝ) (hL : 0 < L)
    (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ) {σ : ℝ} (hσ : 0 < σ) (b : ℝ)
    (hb : b ∉ reflectedInteriorKinkExceptional L a x σ) :
    ContinuousAt (reflectedInteriorKinkCoefficient L a x σ) b := by
  have hcorner : ∀ j : ℤ, x + σ * b ≠ (j : ℝ) * L := by
    intro j he
    apply hb
    apply Or.inl
    refine ⟨j, ?_⟩
    exact ((eq_div_iff hσ.ne').mpr (by linarith)).symm
  have hkink : reflectedFold L (x + σ * b) ≠ a := by
    intro he
    obtain ⟨k, hk | hk⟩ := (reflectedFold_eq_iff_lattice L hL (x + σ * b) a
      ⟨ha.1.le, ha.2.le⟩).mp he
    · apply hb
      refine Or.inr (Or.inl ⟨k, ?_⟩)
      exact ((eq_div_iff hσ.ne').mpr (by linarith)).symm
    · apply hb
      refine Or.inr (Or.inr ⟨k, ?_⟩)
      exact ((eq_div_iff hσ.ne').mpr (by linarith)).symm
  have hi : Continuous (fun z : ℝ => x + σ * z) :=
    continuous_const.add (continuous_const.mul continuous_id)
  have hf : Continuous (fun z : ℝ => reflectedFold L (x + σ * z) - a) :=
    ((reflectedFold_continuous L).comp hi).sub continuous_const
  have hs : ContinuousAt (fun z : ℝ => Real.sign (reflectedFold L (x + σ * z) - a)) b := by
    have he : (fun z : ℝ => Real.sign (reflectedFold L (x + σ * z) - a)) =ᶠ[𝓝 b]
        (fun _ => Real.sign (reflectedFold L (x + σ * b) - a)) := by
      rcases lt_or_gt_of_ne (sub_ne_zero.mpr hkink) with hn | hp
      · filter_upwards [hf.continuousAt.tendsto.eventually_lt_const hn] with z hz
        rw [Real.sign_of_neg hz, Real.sign_of_neg hn]
      · filter_upwards [hf.continuousAt.tendsto.eventually_const_lt hp] with z hz
        rw [Real.sign_of_pos hz, Real.sign_of_pos hp]
    exact continuousAt_const.congr_of_eventuallyEq he
  exact hs.mul (ContinuousAt.comp (f := fun z : ℝ => x + σ * z) (g := reflectedFoldSlope L)
    (reflectedFoldSlope_continuousAt L hL _ hcorner) hi.continuousAt)

end TimeTraps.Probability

end
