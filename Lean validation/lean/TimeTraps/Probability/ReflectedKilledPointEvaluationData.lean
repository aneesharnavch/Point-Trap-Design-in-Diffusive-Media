module

public import TimeTraps.Probability.ReflectedKilledL2Interval
public import TimeTraps.Probability.ReflectedGaussianRegularity

@[expose] public section

/-! Positive-time reference density bounds for point evaluation. The
finite bound is the norm of the actual continuous reflected Gaussian
density on the closed interval, at variance 2DT. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal

variable {n : ℕ}

theorem reflectedKilledPointVariance_pos (P : SpectralProblem n) (T : ℝ≥0) (hT : 0 < T) :
    0 < Real.toNNReal (2 * P.diffusivity) * T :=
  mul_pos (Real.toNNReal_pos.mpr (mul_pos (by norm_num) P.diffusivity_pos)) hT

def reflectedKilledPointDensity (P : SpectralProblem n) (T : ℝ≥0) (hT : 0 < T) (x : ℝ) :
    C(Icc (0 : ℝ) P.length, ℝ) where
  toFun y := reflectedGaussianDensity P.length x (Real.toNNReal (2 * P.diffusivity) * T) y
  continuous_toFun := (reflectedGaussianDensity_continuous P.length_pos x
    (reflectedKilledPointVariance_pos P T hT)).comp continuous_subtype_val

theorem reflectedKilledPointDensity_bound (P : SpectralProblem n) (T : ℝ≥0) (hT : 0 < T)
    (x : ℝ) {y : ℝ} (hy : y ∈ Icc 0 P.length) :
    0 ≤ reflectedGaussianDensity P.length x (Real.toNNReal (2 * P.diffusivity) * T) y ∧
      reflectedGaussianDensity P.length x (Real.toNNReal (2 * P.diffusivity) * T) y ≤
        ‖reflectedKilledPointDensity P T hT x‖ := by
  have hn := (reflectedGaussianDensity_pos P.length_pos x (reflectedKilledPointVariance_pos P T hT) y).le
  refine ⟨hn, ?_⟩
  have he := (reflectedKilledPointDensity P T hT x).norm_coe_le_norm ⟨y, hy⟩
  change ‖reflectedGaussianDensity P.length x (Real.toNNReal (2 * P.diffusivity) * T) y‖ ≤ _ at he
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn] using he

theorem reflectedKilledPoint_kernel_sq_bound (P : SpectralProblem n) (T : ℝ≥0) (hT : 0 < T)
    (x : ℝ) (f : C(Icc (0 : ℝ) P.length, ℝ)) :
    (∫ y, (reflectedFellerExtension P.length P.length_pos f y) ^ 2
      ∂reflectedGaussianLaw P.length x (Real.toNNReal (2 * P.diffusivity) * T)) ≤
      ‖reflectedKilledPointDensity P T hT x‖ *
        ∫ y in Ioo 0 P.length, (reflectedFellerExtension P.length P.length_pos f y) ^ 2 := by
  let v := Real.toNNReal (2 * P.diffusivity) * T
  let g := reflectedFellerExtension P.length P.length_pos f
  let k := reflectedGaussianDensity P.length x v
  have hv : 0 < v := reflectedKilledPointVariance_pos P T hT
  have hk : Continuous k := reflectedGaussianDensity_continuous P.length_pos x hv
  have hi : IntegrableOn (fun y => k y * (g y) ^ 2) (Ioo 0 P.length) :=
    ((hk.mul (g.continuous.pow 2)).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hg : IntegrableOn (fun y => (g y) ^ 2) (Ioo 0 P.length) :=
    ((g.continuous.pow 2).continuousOn.integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have he : (∫ y, (g y) ^ 2 ∂reflectedGaussianLaw P.length x v) =
      ∫ y in Ioo 0 P.length, k y * (g y) ^ 2 := by
    rw [reflectedGaussianLaw_density P.length P.length_pos x hv.ne']
    simpa only [k, reflectedGaussianDensity, smul_eq_mul] using
      integral_withDensity_eq_integral_toReal_smul (reflectedGaussianKernel_measurable P.length x v)
        (Eventually.of_forall (fun y => lt_top_iff_ne_top.mpr
          (reflectedGaussianKernel_ne_top P.length_pos x hv y))) (fun y => (g y) ^ 2)
  change (∫ y, (g y) ^ 2 ∂reflectedGaussianLaw P.length x v) ≤ _
  rw [he, ← integral_const_mul]
  apply integral_mono_ae hi (hg.const_mul _)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
  exact mul_le_mul_of_nonneg_right
    (reflectedKilledPointDensity_bound P T hT x (Ioo_subset_Icc_self hy)).2 (sq_nonneg _)

end TimeTraps.Probability

end
