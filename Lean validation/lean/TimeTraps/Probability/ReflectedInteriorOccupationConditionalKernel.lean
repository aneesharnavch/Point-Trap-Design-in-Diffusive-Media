module

public import TimeTraps.Probability.ReflectedInteriorOccupationConditionalAlgebra

@[expose] public section

/-! The actual interior occupation increment has the integrated reflected
Gaussian density as its conditional mean, given the original Brownian
past. This is derived from the actual test formula, stochastic cutoff
consistency, and the established transition and unconditional mean laws.
The level and the two deterministic times are fixed before the AE claim;
no shift-additivity or PCAF property is presumed. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

theorem reflectedInteriorOccupationTest_fold_bound (L : ℝ) (hL : 0 < L) (a : ℝ) :
    ∃ M : ℝ, ∀ z, |reflectedInteriorOccupationTest L a (reflectedFold L z)| ≤ M := by
  let V : C(Icc (0 : ℝ) L, ℝ) := ⟨fun y => reflectedInteriorOccupationTest L a y.val,
    (reflectedInteriorOccupationTest_continuous L a).comp continuous_subtype_val⟩
  refine ⟨‖V‖, fun z => ?_⟩
  exact V.norm_coe_le_norm ⟨reflectedFold L z, reflectedFold_mem L hL z⟩

theorem reflectedInteriorOccupationTest_gaussian_mean (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    ((∫ y, reflectedInteriorOccupationTest L a (reflectedFold L y)
        ∂reflectedGaussianLaw L x (Real.toNNReal (2 * D) * T)) -
      reflectedInteriorOccupationTest L a (reflectedFold L x) + 2 * D * T.val / L) / (2 * D) =
        ∫ r in (0 : ℝ)..T.val, reflectedGaussianDensity L x (2 * D * r).toNNReal a := by
  let I := brownianStochasticIntegral (reflectedInteriorOccupationTestIntegrand L hL D hD a ha x T)
  have hi : Integrable I brownianDyadicMeasure := (Lp.memLp _).integrable (by norm_num)
  have hv := (reflectedInteriorOccupationTest_memLp L hL D x a T).integrable (by norm_num)
  have he := ((reflectedInteriorOccupationCoefficient_memLp L hL D hD x a T).integrable
    (by norm_num)).const_mul (2 * D)
  have hc : Integrable (fun _ : ℕ → ℝ => 2 * D * T.val / L) brownianDyadicMeasure := integrable_const _
  have hformula := integral_congr_ae (reflectedInteriorOccupationTest_formula L hL D hD a ha x T)
  have hs := integral_add (hi.sub hc) he
  have ht := integral_sub hi hc
  simp only [Pi.sub_apply] at hs ht
  rw [integral_sub hv (integrable_const _), hs, ht] at hformula
  have hmean : (∫ ω, I ω ∂brownianDyadicMeasure) = 0 := brownianStochasticIntegral_mean _
  rw [hmean] at hformula
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul] at hformula
  rw [reflectedInteriorOccupationCoefficient_gaussian_mean L hL D hD x a T] at hformula
  have hfold : (fun ω => reflectedInteriorOccupationTest L a
      (reflectedFold L (foldedTrajectory L D x brownianDyadicPath T ω))) =
      (fun ω => reflectedInteriorOccupationTest L a (foldedTrajectory L D x brownianDyadicPath T ω)) := by
    funext ω
    rw [reflectedFold_eq_self L hL _ (foldedTrajectory_mem L hL D x brownianDyadicPath T ω)]
  have hlaw := (foldedTrajectory_gaussian_hasLaw brownianDyadicPath_isPreBrownianReal L D hD x T).integral_comp
    (((reflectedInteriorOccupationTest_continuous L a).comp (reflectedFold_continuous L)).aestronglyMeasurable)
  simp only [Function.comp_def] at hlaw
  rw [hfold] at hlaw
  rw [hlaw] at hformula
  apply (div_eq_iff (ne_of_gt (mul_pos (by norm_num) hD))).mpr
  linarith

theorem reflectedInteriorOccupationCoefficient_increment_condExp_gaussian
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a : ℝ) (ha : a ∈ Ioo 0 L) (x : ℝ)
    {s t : ℝ≥0} (hst : s ≤ t) :
    brownianDyadicMeasure[fun ω =>
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a t ω -
      reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L a s ω | brownianFiltration s]
        =ᵐ[brownianDyadicMeasure] fun ω =>
      ∫ r in (0 : ℝ)..(t - s).val,
        reflectedGaussianDensity L (foldedTrajectory L D x brownianDyadicPath s ω)
          (2 * D * r).toNNReal a := by
  obtain ⟨M, hM⟩ := reflectedInteriorOccupationTest_fold_bound L hL a
  have hm := ((reflectedInteriorOccupationTest_continuous L a).comp (reflectedFold_continuous L)).measurable
  have hk := foldedTrajectory_condExp brownianDyadicPath_isPreBrownianReal brownianDyadicPath_measurable
    L hL D hD x hst hm hM
  simp only [Function.comp_def] at hk
  have hfold : (fun ω => reflectedInteriorOccupationTest L a
      (reflectedFold L (foldedTrajectory L D x brownianDyadicPath t ω))) =
      (fun ω => reflectedInteriorOccupationTest L a (foldedTrajectory L D x brownianDyadicPath t ω)) := by
    funext ω
    rw [reflectedFold_eq_self L hL _ (foldedTrajectory_mem L hL D x brownianDyadicPath t ω)]
  rw [hfold] at hk
  change brownianDyadicMeasure[fun ω => reflectedInteriorOccupationTest L a
      (foldedTrajectory L D x brownianDyadicPath t ω) | brownianFiltration s] =ᵐ[brownianDyadicMeasure]
    (fun ω => ∫ y, reflectedInteriorOccupationTest L a (reflectedFold L y)
      ∂reflectedGaussianLaw L (foldedTrajectory L D x brownianDyadicPath s ω)
        (Real.toNNReal (2 * D) * (t - s))) at hk
  filter_upwards [reflectedInteriorOccupationCoefficient_increment_condExp_algebra L hL D hD a ha x hst,
    hk] with ω he hkernel
  rw [he, hkernel]
  have hmean := reflectedInteriorOccupationTest_gaussian_mean L hL D hD a ha
    (foldedTrajectory L D x brownianDyadicPath s ω) (t - s)
  rw [reflectedFold_eq_self L hL _ (foldedTrajectory_mem L hL D x brownianDyadicPath s ω)] at hmean
  have hlen : (t - s).val = t.val - s.val := NNReal.coe_sub hst
  exact (congrArg (fun q : ℝ =>
    ((∫ y, reflectedInteriorOccupationTest L a (reflectedFold L y)
      ∂reflectedGaussianLaw L (foldedTrajectory L D x brownianDyadicPath s ω)
        (Real.toNNReal (2 * D) * (t - s))) -
      reflectedInteriorOccupationTest L a (foldedTrajectory L D x brownianDyadicPath s ω) +
      2 * D * q / L) / (2 * D)) hlen.symm).trans hmean

end TimeTraps.Probability
