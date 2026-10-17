module

public import TimeTraps.Probability.ReflectedFiniteKinkC2Moments
public import TimeTraps.Probability.ReflectedFiniteKinkC2Formula

@[expose] public section

/-! Expected values in the actual finite-kink reflected Itô–Tanaka
formula. All terms are integrable by the proved L² bounds. The interior
occupation coefficient has physical factor 2D, and boundary terms use
the actual endpoint slopes. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

theorem reflectedFiniteKinkC2_expected_value (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, finiteKinkPotential F Finset.univ a c
      (foldedTrajectory L D x brownianDyadicPath T ω) ∂brownianDyadicMeasure) =
      finiteKinkPotential F Finset.univ a c (reflectedFold L x) +
        D * (∫ ω, reflectedC2ItoDrift F brownianDyadicPath L D x T ω ∂brownianDyadicMeasure) +
        (∑ i, c i * ∫ ω, reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) T ω
          ∂brownianDyadicMeasure) +
        finiteKinkSlope F Finset.univ a c 0 *
          (∫ ω, affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω ∂brownianDyadicMeasure) -
        finiteKinkSlope F Finset.univ a c L *
          (∫ ω, affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T ω ∂brownianDyadicMeasure) := by
  have hv := (reflectedFiniteKinkC2_value_memLp hF L hL D x a c T).integrable (by norm_num)
  have hI := (reflectedFiniteKinkC2Integral_memLp hF L hL D hD a c ha x T).integrable (by norm_num)
  have hd := ((reflectedC2ItoDrift_memLp (P := brownianDyadicMeasure) hF
    brownianDyadicPath_jointly_measurable L hL D x T).integrable (by norm_num)).const_mul D
  have hC := (reflectedFiniteKinkC2_correction_sum_memLp L hL D hD x a c T).integrable (by norm_num)
  have h0 := ((reflectedLowerRegulator_memLp L hL D hD x T).integrable (by norm_num)).const_mul
    (finiteKinkSlope F Finset.univ a c 0)
  have hLr := ((reflectedUpperRegulator_memLp L hL D hD x T).integrable (by norm_num)).const_mul
    (finiteKinkSlope F Finset.univ a c L)
  have he := integral_congr_ae (reflectedFiniteKinkC2_formula hF L hL D hD a c ha x T)
  have hs := integral_sub (((hI.add hd).add hC).add h0) hLr
  have h₁ := integral_add ((hI.add hd).add hC) h0
  have h₂ := integral_add (hI.add hd) hC
  have h₃ := integral_add hI hd
  simp only [Pi.add_apply] at hs h₁ h₂ h₃
  rw [integral_sub hv (integrable_const _), hs, h₁, h₂, h₃,
    reflectedFiniteKinkC2Integral_mean hF L hL D hD a c ha x T] at he
  have hsum : (∫ ω, ∑ i, c i * reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) T ω
      ∂brownianDyadicMeasure) =
      ∑ i, c i * ∫ ω, reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) T ω
        ∂brownianDyadicMeasure := by
    rw [integral_finsetSum Finset.univ (fun i _ =>
      ((reflectedInteriorCorrection_memLp L hL D hD x (a i) T).integrable (by norm_num)).const_mul (c i))]
    simp only [integral_const_mul]
  rw [hsum] at he
  simp only [integral_const, probReal_univ, one_smul, integral_const_mul, zero_add] at he
  linarith

theorem reflectedFiniteKinkC2_expected_occupation_value (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, finiteKinkPotential F Finset.univ a c
      (foldedTrajectory L D x brownianDyadicPath T ω) ∂brownianDyadicMeasure) =
      finiteKinkPotential F Finset.univ a c (reflectedFold L x) +
        D * (∫ ω, reflectedC2ItoDrift F brownianDyadicPath L D x T ω ∂brownianDyadicMeasure) +
        2 * D * (∑ i, c i * ∫ ω,
          reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) T ω
          ∂brownianDyadicMeasure) +
        finiteKinkSlope F Finset.univ a c 0 *
          (∫ ω, affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω ∂brownianDyadicMeasure) -
        finiteKinkSlope F Finset.univ a c L *
          (∫ ω, affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T ω ∂brownianDyadicMeasure) := by
  have hn (i : ι) : (∫ ω, reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) T ω
      ∂brownianDyadicMeasure) =
      2 * D * ∫ ω, reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) T ω
        ∂brownianDyadicMeasure := by
    calc
      _ = ∫ ω, (2 * D) * reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) T ω
          ∂brownianDyadicMeasure := by
        apply integral_congr_ae
        filter_upwards [] with ω
        have h := reflectedInteriorOccupationCoefficient_normalization x
          (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) L (a i) T ω
        rw [Real.sq_sqrt (by positivity)] at h
        exact h.symm
      _ = _ := integral_const_mul _ _
  have hsum : (∑ i, c i * ∫ ω, reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) T ω
      ∂brownianDyadicMeasure) =
      2 * D * ∑ i, c i * ∫ ω,
        reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) T ω
        ∂brownianDyadicMeasure := by
    simp only [hn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [reflectedFiniteKinkC2_expected_value hF L hL D hD a c ha x T, hsum]

end TimeTraps.Probability
