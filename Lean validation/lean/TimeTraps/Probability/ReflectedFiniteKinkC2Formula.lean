module

public import TimeTraps.Probability.ReflectedFiniteKinkC2Coefficient
public import TimeTraps.Probability.ReflectedItoC2Formula
public import TimeTraps.Probability.ReflectedInteriorTanakaFormula

@[expose] public section

/-! Actual reflected Itô–Tanaka for a globally C² test plus a finite
family of interior kinks. The signed coefficients, repeated sites and
empty finite family are retained. All terms come from proved actual
stochastic integrals and actual local-time corrections. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

theorem reflectedFiniteKinkC2_formula (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    (fun ω => finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
      finiteKinkPotential F Finset.univ a c (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianStochasticIntegral
        (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T) ω +
        D * reflectedC2ItoDrift F brownianDyadicPath L D x T ω +
        (∑ i, c i * reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) T ω) +
        finiteKinkSlope F Finset.univ a c 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω -
        finiteKinkSlope F Finset.univ a c L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T ω) := by
  have hσ : 0 < Real.sqrt (2 * D) := Real.sqrt_pos.mpr (by positivity)
  have hall : ∀ᵐ ω ∂brownianDyadicMeasure, ∀ i : ι,
      |foldedTrajectory L D x brownianDyadicPath T ω - a i| - |reflectedFold L x - a i| =
        reflectedInteriorKinkIntegral brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
          brownianDyadicPath_jointly_measurable L hL (a i) (ha i) x hσ T ω +
        reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) T ω -
        affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω -
        affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T ω :=
    ae_all_iff.mpr (fun i => reflectedInteriorTanaka_formula L hL (a i) (ha i) x hσ T)
  filter_upwards [reflectedItoC2_formula hF L hL D hD x T,
    reflectedFiniteKinkC2Integral_sum_ae hF L hL D hD a c ha x T, hall] with ω hf hi hk
  have hs := Finset.sum_congr (s₁ := (Finset.univ : Finset ι)) rfl
    (fun i _ => congrArg (fun z : ℝ => c i * z) (hk i))
  simp only [mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul] at hs
  rw [reflectedFiniteKinkSlope_zero F L a c ha, reflectedFiniteKinkSlope_right F L a c ha]
  simp only [finiteKinkPotential]
  linear_combination hf + hs - hi

theorem reflectedFiniteKinkC2_occupation_formula (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    (fun ω => finiteKinkPotential F Finset.univ a c (foldedTrajectory L D x brownianDyadicPath T ω) -
      finiteKinkPotential F Finset.univ a c (reflectedFold L x)) =ᵐ[brownianDyadicMeasure]
      (fun ω => brownianStochasticIntegral
        (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T) ω +
        D * reflectedC2ItoDrift F brownianDyadicPath L D x T ω +
        2 * D * (∑ i, c i * reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) T ω) +
        finiteKinkSlope F Finset.univ a c 0 * affineBrownianLowerRegulator x (Real.sqrt (2 * D)) L T ω -
        finiteKinkSlope F Finset.univ a c L * affineBrownianUpperRegulator x (Real.sqrt (2 * D)) L T ω) := by
  filter_upwards [reflectedFiniteKinkC2_formula hF L hL D hD a c ha x T] with ω hω
  have hs : (∑ i, c i * reflectedInteriorCorrection x (Real.sqrt (2 * D)) L (a i) T ω) =
      2 * D * ∑ i, c i * reflectedInteriorOccupationCoefficient x (Real.sqrt (2 * D)) L (a i) T ω := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    have he := reflectedInteriorOccupationCoefficient_normalization x
      (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) L (a i) T ω
    rw [Real.sq_sqrt (by positivity)] at he
    rw [← he]
    ring
  rw [hs] at hω
  exact hω

end TimeTraps.Probability
