module

public import TimeTraps.Probability.DyadicStieltjesIntegral

@[expose] public section

/-! A regulator measure supported where a path has one fixed value
integrates every spatial test as that value times its mass. Continuous
left dyadic sums converge to this actual boundary integral. -/

namespace TimeTraps.Probability

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem stieltjes_integral_of_supported_level (K : StieltjesFunction ℝ)
    (X : ℝ → ℝ) (a : ℝ) (hs : K.measure.support ⊆ {r | X r = a})
    (g : ℝ → ℝ) (T : ℝ≥0) :
    (∫ r in Ioc (0 : ℝ) T.val, g (X r) ∂K.measure) = g a * (K T.val - K 0) := by
  have he : (fun r => g (X r)) =ᵐ[K.measure.restrict (Ioc (0 : ℝ) T.val)] (fun _ => g a) := by
    filter_upwards [ae_restrict_of_ae K.measure.support_mem_ae] with r hr
    rw [hs hr]
  rw [integral_congr_ae he, integral_const]
  simp only [Measure.real, Measure.restrict_apply_univ, StieltjesFunction.measure_Ioc,
    smul_eq_mul, mul_comm]
  congr 1
  exact ENNReal.toReal_ofReal (sub_nonneg.mpr (K.mono T.coe_nonneg))

theorem dyadicStieltjesSum_supported_level_tendsto (K : StieltjesFunction ℝ)
    (X : ℝ≥0 → ℝ) (hX : Continuous X) (a : ℝ)
    (hs : K.measure.support ⊆ {r : ℝ | X r.toNNReal = a})
    (g : ℝ → ℝ) (hg : Continuous g) (T : ℝ≥0) :
    Tendsto (dyadicStieltjesSum K (fun t => g (X t)) T) atTop
      (𝓝 (g a * (K T.val - K 0))) := by
  have he := stieltjes_integral_of_supported_level K (fun r => X r.toNNReal) a hs g T
  simpa only [he] using dyadicStieltjesSum_tendsto K (fun t => g (X t)) (hg.comp hX) T

end TimeTraps.Probability
