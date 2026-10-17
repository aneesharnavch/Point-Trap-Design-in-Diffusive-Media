module

public import TimeTraps.Probability.ReflectedC2ItoEnergy
public import TimeTraps.Probability.ReflectedInteriorKinkIntegrand

@[expose] public section

/-! The actual original-Brownian integrand for a smooth reflected test
plus a finite family of interior absolute-value kinks. Coefficients may
be signed, sites may repeat, and the finite index type may be empty. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis
open scoped NNReal ENNReal Topology

variable {ι : Type*} [Fintype ι] {F : ℝ → ℝ}

def reflectedFiniteKinkC2Integrand (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) : BrownianIntegrand :=
  reflectedC2ItoIntegrand hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
    brownianDyadicPath_jointly_measurable L hL D hD x T +
      ∑ i, c i • reflectedInteriorKinkIntegrand brownianDyadicPath_isBrownianReal
        brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL (a i) (ha i) x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T

theorem reflectedFiniteKinkC2Integrand_integral (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    brownianStochasticIntegral (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T) =
      reflectedC2ItoIntegral hF brownianDyadicPath_isBrownianReal brownianDyadicPath_measurable
        brownianDyadicPath_jointly_measurable L hL D hD x T +
      ∑ i, c i • reflectedInteriorKinkIntegral brownianDyadicPath_isBrownianReal
        brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL (a i) (ha i) x
        (Real.sqrt_pos.mpr (show 0 < 2 * D by positivity)) T := by
  unfold reflectedFiniteKinkC2Integrand
  rw [map_add, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul]
  rfl

theorem reflectedFiniteKinkC2Integrand_cutoff (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T t : ℝ≥0) :
    brownianTimeCutoff brownianDyadicPath brownianDyadicPath_measurable brownianDyadicMeasure t
      (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T) =
        reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x (min t T) := by
  unfold reflectedFiniteKinkC2Integrand
  simp only [map_add, map_sum, map_smul, reflectedC2ItoIntegrand_cutoff,
    reflectedInteriorKinkIntegrand_cutoff]

theorem reflectedFiniteKinkC2Integral_memLp (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    MemLp (brownianStochasticIntegral
      (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T)) 2 brownianDyadicMeasure :=
  Lp.memLp _

theorem reflectedFiniteKinkC2Integral_mean (hF : ContDiff ℝ 2 F)
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (a c : ι → ℝ)
    (ha : ∀ i, a i ∈ Ioo 0 L) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, brownianStochasticIntegral
      (reflectedFiniteKinkC2Integrand hF L hL D hD a c ha x T) ω ∂brownianDyadicMeasure) = 0 :=
  brownianStochasticIntegral_mean _

end TimeTraps.Probability

end
