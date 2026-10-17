module

public import TimeTraps.Probability.ReflectedAtomicHazardData
public import TimeTraps.Probability.ReflectedC2ItoDrift

@[expose] public section

/-! The literal survival-weighted ordinary curvature integral is jointly
measurable and square integrable. Its bound uses only continuity of F''
on the compact folded range and 0 < W ≤ 1; no global derivative bound,
third derivative or Neumann condition is required. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

def reflectedAtomicWeightedCurvatureProcess (F : ℝ → ℝ) (L D x : ℝ) (a κ : ι → ℝ)
    (t : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  reflectedAtomicSurvival L D x a κ t ω *
    deriv (deriv F) (foldedTrajectory L D x brownianDyadicPath t ω)

def reflectedAtomicWeightedCurvature (F : ℝ → ℝ) (L D x : ℝ) (a κ : ι → ℝ)
    (T : ℝ≥0) (ω : ℕ → ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..T.val, reflectedAtomicWeightedCurvatureProcess F L D x a κ r.toNNReal ω

theorem reflectedAtomicWeightedCurvatureProcess_jointlyMeasurable (hF : ContDiff ℝ 2 F)
    (L D x : ℝ) (a κ : ι → ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) =>
      reflectedAtomicWeightedCurvatureProcess F L D x a κ p.1 p.2) := by
  have hc : Continuous (deriv (deriv F)) :=
    (show ContDiff ℝ 1 (deriv F) from hF.deriv').continuous_deriv (by norm_num)
  have hx := foldedTrajectory_joint_measurable L D x brownianDyadicPath brownianDyadicPath_jointly_measurable
  have hq := hc.measurable.comp hx
  exact (reflectedAtomicSurvival_jointlyMeasurable L D x a κ).mul hq

theorem reflectedAtomicWeightedCurvatureProcess_bound (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (t : ℝ≥0) (ω : ℕ → ℝ) :
    |reflectedAtomicWeightedCurvatureProcess F L D x a κ t ω| ≤ ‖reflectedC2CurvatureMap hF L‖ := by
  have hw := reflectedAtomicSurvival_bounds L hD x a κ hκ t ω
  have hq := reflectedC2_curvature_bound hF brownianDyadicPath L hL D x t ω
  unfold reflectedAtomicWeightedCurvatureProcess
  rw [abs_mul, abs_of_pos hw.1]
  calc
    _ ≤ 1 * ‖reflectedC2CurvatureMap hF L‖ :=
      mul_le_mul hw.2 hq (abs_nonneg _) zero_le_one
    _ = _ := one_mul _

theorem reflectedAtomicWeightedCurvature_jointlyMeasurable (hF : ContDiff ℝ 2 F)
    (L D x : ℝ) (a κ : ι → ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedAtomicWeightedCurvature F L D x a κ p.1 p.2) := by
  have hm : Measurable (fun p : ℝ × (ℕ → ℝ) => (p.1.toNNReal, p.2)) :=
    measurable_fst.real_toNNReal.prodMk measurable_snd
  have hH := (reflectedAtomicWeightedCurvatureProcess_jointlyMeasurable hF L D x a κ).comp hm
  have hi := timeIntegral_jointlyMeasurable hH
  exact hi

theorem reflectedAtomicWeightedCurvature_intervalIntegrable (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (ω : ℕ → ℝ) :
    IntervalIntegrable (fun r : ℝ =>
      reflectedAtomicWeightedCurvatureProcess F L D x a κ r.toNNReal ω) volume 0 T.val := by
  have hm : Measurable (fun t : ℝ≥0 => reflectedAtomicWeightedCurvatureProcess F L D x a κ t ω) :=
    Measurable.of_uncurry_right (f := fun t ω => reflectedAtomicWeightedCurvatureProcess F L D x a κ t ω)
      (y := ω) (reflectedAtomicWeightedCurvatureProcess_jointlyMeasurable hF L D x a κ)
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le T.coe_nonneg).mpr
  apply (integrable_const ‖reflectedC2CurvatureMap hF L‖).mono'
    (hm.comp measurable_real_toNNReal).aestronglyMeasurable
  exact Eventually.of_forall (fun r => by
    simpa only [Real.norm_eq_abs, Function.comp_def] using
      reflectedAtomicWeightedCurvatureProcess_bound hF L hL D hD x a κ hκ r.toNNReal ω)

theorem reflectedAtomicWeightedCurvature_bound (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) (ω : ℕ → ℝ) :
    |reflectedAtomicWeightedCurvature F L D x a κ T ω| ≤ T.val * ‖reflectedC2CurvatureMap hF L‖ := by
  have hb := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := T.val)
    (fun r _ => show ‖reflectedAtomicWeightedCurvatureProcess F L D x a κ r.toNNReal ω‖ ≤
      ‖reflectedC2CurvatureMap hF L‖ from by
        simpa only [Real.norm_eq_abs] using
          reflectedAtomicWeightedCurvatureProcess_bound hF L hL D hD x a κ hκ r.toNNReal ω)
  rw [Real.norm_eq_abs, sub_zero] at hb
  have hT : |T.val| = T.val := abs_of_nonneg T.coe_nonneg
  exact hb.trans_eq ((congrArg (fun z : ℝ => ‖reflectedC2CurvatureMap hF L‖ * z) hT).trans (mul_comm _ _))

theorem reflectedAtomicWeightedCurvature_memLp (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (a κ : ι → ℝ)
    (hκ : ∀ i, 0 ≤ κ i) (T : ℝ≥0) :
    MemLp (reflectedAtomicWeightedCurvature F L D x a κ T) 2 brownianDyadicMeasure := by
  have hφ : Measurable (fun ω : ℕ → ℝ => (T, ω)) := measurable_const.prodMk measurable_id
  have hm := (reflectedAtomicWeightedCurvature_jointlyMeasurable hF L D x a κ).comp hφ
  exact MemLp.of_bound hm.aestronglyMeasurable (T.val * ‖reflectedC2CurvatureMap hF L‖)
    (Eventually.of_forall (reflectedAtomicWeightedCurvature_bound hF L hL D hD x a κ hκ T))

end TimeTraps.Probability

end
