module

public import TimeTraps.Probability.ReflectedItoRegulatorMoments
public import TimeTraps.Probability.ReflectedC2ItoEnergy

@[expose] public section

/-! Uniform second moments of the actual reflected lower regulator,
derived from its quadratic Itô identity and the constructed integral's isometry. -/

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

theorem reflectedLowerBoundaryTest_bounds (L : ℝ) (hL : 0 < L) {z : ℝ}
    (hz : z ∈ Icc 0 L) :
    0 ≤ reflectedLowerBoundaryTest L z ∧ reflectedLowerBoundaryTest L z ≤ L := by
  have hs : z ^ 2 / (2 * L) ≤ z := (div_le_iff₀ (by positivity)).mpr
    (by nlinarith [mul_nonneg hz.1 (sub_nonneg.mpr hz.2)])
  have hsq : 0 ≤ z ^ 2 / (2 * L) := by positivity
  unfold reflectedLowerBoundaryTest reflectedUpperBoundaryTest
  constructor <;> linarith [hz.2]

theorem reflectedLowerBoundaryTest_derivativeMap_norm_le (L : ℝ) (hL : 0 < L) :
    ‖reflectedC2DerivativeMap (reflectedLowerBoundaryTest_contDiff L) L‖ ≤ 1 := by
  let : Nonempty (Icc (0 : ℝ) L) := ⟨⟨0, by simp [hL.le]⟩⟩
  apply (reflectedC2DerivativeMap (reflectedLowerBoundaryTest_contDiff L) L).norm_le_of_nonempty.mpr
  intro z
  change ‖deriv (reflectedLowerBoundaryTest L) z.val‖ ≤ 1
  rw [reflectedLowerBoundaryTest_deriv L hL, Real.norm_eq_abs]
  have hq : 0 ≤ z.val / L := div_nonneg z.property.1 hL.le
  have hq1 : z.val / L ≤ 1 := (div_le_one hL).mpr z.property.2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem reflectedLowerRegulator_secondMoment_uniform_bound (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω ^ 2
      ∂brownianDyadicMeasure) ≤ 3 * L ^ 2 + 6 * D * T.val + 3 * (D * T.val / L) ^ 2 := by
  let I : (ℕ → ℝ) → ℝ := fun ω => reflectedC2ItoIntegral
    (reflectedLowerBoundaryTest_contDiff L) brownianDyadicPath_isBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x T ω
  let V : (ℕ → ℝ) → ℝ := fun ω =>
    reflectedLowerBoundaryTest L (foldedTrajectory L D x brownianDyadicPath T ω) -
      reflectedLowerBoundaryTest L (reflectedFold L x)
  let c : ℝ := D * T.val / L
  have hI2 : Integrable (fun ω => I ω ^ 2) brownianDyadicMeasure :=
    (reflectedC2ItoIntegral_memLp (reflectedLowerBoundaryTest_contDiff L) L hL D hD x T).integrable_sq
  have hV (ω : ℕ → ℝ) : (V ω) ^ 2 ≤ L ^ 2 := by
    have hb := reflectedLowerBoundaryTest_bounds L hL
      (reflectedFold_mem L hL (x + Real.sqrt (2 * D) * brownianDyadicPath T ω))
    have hx := reflectedLowerBoundaryTest_bounds L hL (reflectedFold_mem L hL x)
    change 0 ≤ reflectedLowerBoundaryTest L (foldedTrajectory L D x brownianDyadicPath T ω) ∧
      reflectedLowerBoundaryTest L (foldedTrajectory L D x brownianDyadicPath T ω) ≤ L at hb
    have hv : |V ω| ≤ L := abs_le.mpr ⟨by dsimp [V]; linarith, by dsimp [V]; linarith⟩
    nlinarith [sq_abs (V ω), abs_nonneg (V ω)]
  have hb : (∫ ω, affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω ^ 2
      ∂brownianDyadicMeasure) ≤ ∫ ω, 3 * (L ^ 2 + I ω ^ 2 + c ^ 2) ∂brownianDyadicMeasure := by
    apply integral_mono_ae (reflectedLowerRegulator_memLp L hL D hD x T).integrable_sq
      ((((integrable_const (L ^ 2)).add hI2).add (integrable_const (c ^ 2))).const_mul 3)
    filter_upwards [reflectedLowerRegulator_quadratic_ae L hL D hD x T] with ω hω
    change affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω = V ω - I ω + c at hω
    change affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω ^ 2 ≤ 3 * (L ^ 2 + I ω ^ 2 + c ^ 2)
    rw [hω]
    nlinarith [hV ω, sq_nonneg (V ω + I ω), sq_nonneg (V ω - c), sq_nonneg (I ω + c)]
  have hIe : (∫ ω, I ω ^ 2 ∂brownianDyadicMeasure) ≤ 2 * D * T.val := by
    have he := reflectedC2ItoIntegral_secondMoment_bound (reflectedLowerBoundaryTest_contDiff L) L hL D hD x T
    have hn := reflectedLowerBoundaryTest_derivativeMap_norm_le L hL
    have hn0 := norm_nonneg (reflectedC2DerivativeMap (reflectedLowerBoundaryTest_contDiff L) L)
    have hn2 : ‖reflectedC2DerivativeMap (reflectedLowerBoundaryTest_contDiff L) L‖ ^ 2 ≤ 1 := by nlinarith
    have hfac : 0 ≤ 2 * D * T.val := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hD.le) T.coe_nonneg
    exact he.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hn2 hfac)
  have hs : Integrable (fun ω => L ^ 2 + I ω ^ 2) brownianDyadicMeasure := (integrable_const (L ^ 2)).add hI2
  rw [integral_const_mul, integral_add hs (integrable_const (c ^ 2)),
    integral_add (integrable_const (L ^ 2)) hI2] at hb
  simp only [integral_const, probReal_univ, one_smul] at hb
  dsimp only [c] at hb
  linarith

end TimeTraps.Probability
