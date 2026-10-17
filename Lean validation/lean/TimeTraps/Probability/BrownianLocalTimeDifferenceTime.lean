module

public import TimeTraps.Probability.BrownianLocalTimeNorm

@[expose] public section

/-! Shifted absolute Brownian differences have the Brownian square-root
time modulus in actual L2, uniformly over the spatial level. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownianTanakaDifference_time_bound (B : ℝ≥0 → Ω → ℝ) (a : ℝ) (S T : ℝ≥0) (ω : Ω) :
    |brownianTanakaDifference B a T ω - brownianTanakaDifference B a S ω| ≤ |B T ω - B S ω| := by
  have he : brownianTanakaDifference B a T ω - brownianTanakaDifference B a S ω =
      |B T ω - a| - |B S ω - a| := by
    unfold brownianTanakaDifference
    ring
  rw [he]
  have hd : (B T ω - a) - (B S ω - a) = B T ω - B S ω := by ring
  simpa only [hd] using abs_abs_sub_abs_le_abs_sub (B T ω - a) (B S ω - a)

theorem brownianTanakaDifferenceL2_time_norm_le (hB : IsPreBrownianReal B P)
    (a : ℝ) (S T : ℝ≥0) :
    ‖brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T) -
      brownianTanakaDifferenceL2 B a S (brownianTanakaDifference_memLp hB a S)‖ ≤
        Real.sqrt |T.val - S.val| := by
  let U := brownianTanakaDifferenceL2 B a T (brownianTanakaDifference_memLp hB a T)
  let V := brownianTanakaDifferenceL2 B a S (brownianTanakaDifference_memLp hB a S)
  have hD : (U - V) =ᵐ[P] (fun ω => brownianTanakaDifference B a T ω - brownianTanakaDifference B a S ω) := by
    filter_upwards [Lp.coeFn_sub U V,
      brownianTanakaDifferenceL2_coe B a T (brownianTanakaDifference_memLp hB a T),
      brownianTanakaDifferenceL2_coe B a S (brownianTanakaDifference_memLp hB a S)] with ω hd hu hv
    rw [hd, Pi.sub_apply, hu, hv]
  have hs : ‖U - V‖ ^ 2 ≤ |T.val - S.val| := by
    calc
      _ = ∫ ω, (U - V) ω ^ 2 ∂P := by
        simpa only [Lp.toLp_coeFn] using TimeTraps.Analysis.memLp_norm_toLp_sq (Lp.memLp (U - V))
      _ ≤ ∫ ω, (B T ω - B S ω) ^ 2 ∂P := by
        apply integral_mono_ae (Lp.memLp (U - V)).integrable_sq (brownian_increment_integrable_sq hB S T)
        filter_upwards [hD] with ω hω
        rw [hω]
        simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr
          (brownianTanakaDifference_time_bound B a S T ω)
      _ = _ := brownian_increment_second_moment hB S T
  apply (sq_le_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _)).mp
  exact hs.trans_eq (Real.sq_sqrt (abs_nonneg _)).symm

end TimeTraps.Probability
