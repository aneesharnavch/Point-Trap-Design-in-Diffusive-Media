module

public import TimeTraps.Probability.ReflectedFoldCosine
public import TimeTraps.Probability.ReflectedFoldTrajectory
public import TimeTraps.Probability.BrownianCosineTransition

@[expose] public section

/-! Exact Neumann cosine evolution along the actual folded trajectory with
diffusion scale `sqrt (2D)`. All natural modes and all ordered times are
included, so the constant mode and equal times require no exclusions.
These are cosine-core identities, not a full generator-domain theorem. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem foldedTrajectory_cosine {ι Ω : Type*} (L : ℝ) (hL : 0 < L) (D x : ℝ)
    (B : ι → Ω → ℝ) (n : ℕ) (t : ι) (ω : Ω) :
    Real.cos (((n : ℝ) * Real.pi / L) * foldedTrajectory L D x B t ω) =
      Real.cos (((n : ℝ) * Real.pi / L) * (x + Real.sqrt (2 * D) * B t ω)) :=
  reflectedFold_cosine L hL n _

theorem foldedTrajectory_cosine_condExp (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (n : ℕ) {s t : ℝ≥0} (hst : s ≤ t) :
    P[fun ω => Real.cos (((n : ℝ) * Real.pi / L) * foldedTrajectory L D x B t ω) |
      brownianNaturalFiltration B hBm s] =ᵐ[P]
      fun ω => Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (t.val - s.val)) *
        Real.cos (((n : ℝ) * Real.pi / L) * foldedTrajectory L D x B s ω) := by
  have hc := brownian_affine_cos_condExp hB hBm hst x (Real.sqrt (2 * D))
    ((n : ℝ) * Real.pi / L)
  have he : -(t.val - s.val) * (((n : ℝ) * Real.pi / L) * Real.sqrt (2 * D)) ^ 2 / 2 =
      -D * ((n : ℝ) * Real.pi / L) ^ 2 * (t.val - s.val) := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [he] at hc
  simpa only [foldedTrajectory_cosine L hL] using hc

theorem foldedTrajectory_cosine_integral (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D)
    (x : ℝ) (n : ℕ) (t : ℝ≥0) :
    (∫ ω, Real.cos (((n : ℝ) * Real.pi / L) * foldedTrajectory L D x B t ω) ∂P) =
      Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * t.val) *
        Real.cos (((n : ℝ) * Real.pi / L) * x) := by
  have hc := brownian_affine_cos_integral hB hBm t x (Real.sqrt (2 * D))
    ((n : ℝ) * Real.pi / L)
  have he : -t.val * (((n : ℝ) * Real.pi / L) * Real.sqrt (2 * D)) ^ 2 / 2 =
      -D * ((n : ℝ) * Real.pi / L) ^ 2 * t.val := by
    rw [mul_pow, Real.sq_sqrt (by positivity)]
    ring
  rw [he] at hc
  simpa only [foldedTrajectory_cosine L hL] using hc

theorem brownianDyadicFoldedTrajectory_cosine_condExp (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 < D) (x : ℝ) (n : ℕ) {s t : ℝ≥0} (hst : s ≤ t) :
    brownianDyadicMeasure[fun ω => Real.cos (((n : ℝ) * Real.pi / L) *
      foldedTrajectory L D x brownianDyadicPath t ω) | brownianFiltration s] =ᵐ[brownianDyadicMeasure]
      fun ω => Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (t.val - s.val)) *
        Real.cos (((n : ℝ) * Real.pi / L) * foldedTrajectory L D x brownianDyadicPath s ω) :=
  foldedTrajectory_cosine_condExp brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable L hL D hD x n hst

end TimeTraps.Probability
