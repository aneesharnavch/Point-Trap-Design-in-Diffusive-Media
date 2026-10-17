module

public import TimeTraps.Spectral.LogDerivative
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

@[expose] public section

/-!
Regular cosine comparison for the full interval energy space. Frequencies
strictly below the Dirichlet threshold have a positive denominator even at
the endpoints; the sharp threshold will be reached by continuity.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

noncomputable def dirichletCosine (k c x : ℝ) : ℝ := Real.cos (k * (x - c))

noncomputable def dirichletCosineSlope (k c x : ℝ) : ℝ := -k * Real.sin (k * (x - c))

theorem dirichletCosine_continuous (k c : ℝ) : Continuous (dirichletCosine k c) := by
  unfold dirichletCosine
  fun_prop

theorem dirichletCosineSlope_continuous (k c : ℝ) :
    Continuous (dirichletCosineSlope k c) := by
  unfold dirichletCosineSlope
  fun_prop

theorem dirichletCosine_hasDerivAt (k c x : ℝ) :
    HasDerivAt (dirichletCosine k c) (dirichletCosineSlope k c x) x := by
  have h := (((hasDerivAt_id x).sub_const c).const_mul k).cos
  change HasDerivAt (dirichletCosine k c)
    (-Real.sin (k * (x - c)) * (k * 1)) x at h
  have he : -Real.sin (k * (x - c)) * (k * 1) = dirichletCosineSlope k c x := by
    unfold dirichletCosineSlope
    ring
  rwa [he] at h

theorem dirichletCosineSlope_hasDerivAt (k c x : ℝ) :
    HasDerivAt (dirichletCosineSlope k c) (-(k ^ 2) * dirichletCosine k c x) x := by
  have h := ((((hasDerivAt_id x).sub_const c).const_mul k).sin).const_mul (-k)
  change HasDerivAt (dirichletCosineSlope k c)
    (-k * (Real.cos (k * (x - c)) * (k * 1))) x at h
  have he : -k * (Real.cos (k * (x - c)) * (k * 1)) =
      -(k ^ 2) * dirichletCosine k c x := by
    unfold dirichletCosine
    ring
  rwa [he] at h

theorem dirichletCosine_energy (k c l r : ℝ) (hlr : l ≤ r) :
    IntervalEnergy (dirichletCosine k c) l r :=
  intervalEnergy_of_continuous_derivative hlr
    (dirichletCosine_continuous k c).continuousOn
    (dirichletCosineSlope_continuous k c).continuousOn
    (fun x _ => dirichletCosine_hasDerivAt k c x)

/-- Positive comparison cosines yield a lower bound for every H1 function
whose trace vanishes, or whose comparison slope vanishes, at each end. -/
theorem dirichletCosine_energy_lower_bound {v : ℝ → ℝ} {k c l r : ℝ}
    (hlr : l ≤ r) (hv : IntervalEnergy v l r)
    (hphase : ∀ x ∈ Icc l r, k * (x - c) ∈ Ioo (-(Real.pi / 2)) (Real.pi / 2))
    (hl : v l = 0 ∨ dirichletCosineSlope k c l = 0)
    (hr : v r = 0 ∨ dirichletCosineSlope k c r = 0) :
    k ^ 2 * (∫ x in l..r, v x ^ 2) ≤ ∫ x in l..r, deriv v x ^ 2 := by
  let q := fun x => dirichletCosineSlope k c x / dirichletCosine k c x
  have hp : ∀ x ∈ Icc l r, 0 < dirichletCosine k c x :=
    fun x hx => Real.cos_pos_of_mem_Ioo (hphase x hx)
  have hq : ContinuousOn q (Icc l r) :=
    (dirichletCosineSlope_continuous k c).continuousOn.div
      (dirichletCosine_continuous k c).continuousOn (fun x hx => ne_of_gt (hp x hx))
  have hdq : ∀ x ∈ Ioo l r, HasDerivAt q (-(k ^ 2) - q x ^ 2) x :=
    fun x hx => logarithmic_derivative (ne_of_gt (hp x (Ioo_subset_Icc_self hx)))
      (dirichletCosine_hasDerivAt k c x) (dirichletCosineSlope_hasDerivAt k c x)
  have h := riccati_square_identity hlr hv hq hdq
  have hlq : q l * v l ^ 2 = 0 := by
    rcases hl with hl | hl <;> simp [q, hl]
  have hrq : q r * v r ^ 2 = 0 := by
    rcases hr with hr | hr <;> simp [q, hr]
  rw [hlq, hrq] at h
  have hn : 0 ≤ ∫ x in l..r, (deriv v x - q x * v x) ^ 2 :=
    intervalIntegral.integral_nonneg hlr (fun _ _ => sq_nonneg _)
  linarith

end TimeTraps.Spectral
