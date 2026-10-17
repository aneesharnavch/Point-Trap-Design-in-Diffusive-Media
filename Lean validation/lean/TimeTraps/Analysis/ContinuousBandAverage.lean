module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! Symmetric shrinking interval averages of a continuous Banach-valued
function converge at every center. The coefficient is exactly 1/(2h).
The proof differentiates the genuine Bochner primitive at the center. -/

namespace TimeTraps.Analysis

open MeasureTheory Filter Set
open scoped Topology

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem continuous_band_average_tendsto {f : ℝ → E} (hf : Continuous f) (a : ℝ) :
    Tendsto (fun h : ℝ => (1 / (2 * h)) • ∫ x in (a - h)..(a + h), f x)
      (𝓝[>] 0) (𝓝 (f a)) := by
  let F := fun b => ∫ x in a..b, f x
  have hF (b : ℝ) : HasDerivAt F (f b) b :=
    intervalIntegral.integral_hasDerivAt_right (hf.intervalIntegrable a b)
      hf.aestronglyMeasurable.stronglyMeasurableAtFilter hf.continuousAt
  have hp := (hF (a + 0)).scomp 0 ((hasDerivAt_id (0 : ℝ)).const_add a)
  have hm := (hF (a - 0)).scomp 0 ((hasDerivAt_id (0 : ℝ)).const_sub a)
  have hG := hp.sub hm
  simp only [add_zero, sub_zero, one_smul, neg_one_smul] at hG
  have hG' : HasDerivAt (fun h => F (a + h) - F (a - h)) ((2 : ℝ) • f a) 0 := by
    simpa only [sub_neg_eq_add, two_smul, Function.comp_def, Pi.sub_def] using hG
  have he : (fun h => F (a + h) - F (a - h)) =
      (fun h => ∫ x in (a - h)..(a + h), f x) := by
    funext h
    exact intervalIntegral.integral_interval_sub_left
      (hf.intervalIntegrable a (a + h)) (hf.intervalIntegrable a (a - h))
  rw [he] at hG'
  have hs := hG'.tendsto_slope_zero_right.const_smul (1 / 2 : ℝ)
  simpa [smul_smul, one_div, mul_inv_rev, mul_comm] using hs

theorem continuous_band_average_seq_tendsto {f : ℝ → E} (hf : Continuous f) (a : ℝ)
    {h : ℕ → ℝ} (hpos : ∀ n, 0 < h n) (hlim : Tendsto h atTop (𝓝 0)) :
    Tendsto (fun n => (1 / (2 * h n)) • ∫ x in (a - h n)..(a + h n), f x)
      atTop (𝓝 (f a)) :=
  (continuous_band_average_tendsto hf a).comp
    (tendsto_nhdsWithin_iff.mpr ⟨hlim, Eventually.of_forall hpos⟩)

end TimeTraps.Analysis
