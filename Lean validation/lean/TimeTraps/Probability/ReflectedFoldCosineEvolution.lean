module

public import TimeTraps.Probability.ReflectedFoldCosineTransition
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! The scalar eigenfunction calculus behind the proved folded cosine
transition: exact Neumann endpoint derivatives, spatial eigenvalue,
semigroup multiplication, and time derivative. No density or full
generator-domain identification is asserted. -/

namespace TimeTraps.Probability

theorem reflectedCosine_derivative (L : ℝ) (n : ℕ) (z : ℝ) :
    HasDerivAt (fun y : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * y))
      (-Real.sin (((n : ℝ) * Real.pi / L) * z) * ((n : ℝ) * Real.pi / L)) z := by
  simpa only [id_eq, mul_one] using (((hasDerivAt_id z).const_mul ((n : ℝ) * Real.pi / L)).cos)

theorem reflectedCosine_neumann_left (L : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * y)) 0 0 := by
  simpa using reflectedCosine_derivative L n 0

theorem reflectedCosine_neumann_right (L : ℝ) (hL : 0 < L) (n : ℕ) :
    HasDerivAt (fun y : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * y)) 0 L := by
  simpa only [div_mul_cancel₀ _ hL.ne', Real.sin_nat_mul_pi, neg_zero, zero_mul]
    using reflectedCosine_derivative L n L

theorem reflectedCosine_spatial_eigenvalue (L D : ℝ) (n : ℕ) (z : ℝ) :
    D * deriv (deriv (fun y : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * y))) z =
      -D * ((n : ℝ) * Real.pi / L) ^ 2 * Real.cos (((n : ℝ) * Real.pi / L) * z) := by
  have hf : deriv (fun y : ℝ => Real.cos (((n : ℝ) * Real.pi / L) * y)) =
      (fun y => -Real.sin (((n : ℝ) * Real.pi / L) * y) * ((n : ℝ) * Real.pi / L)) :=
    funext (fun y => (reflectedCosine_derivative L n y).deriv)
  rw [hf]
  have hd := ((((hasDerivAt_id z).const_mul ((n : ℝ) * Real.pi / L)).sin).neg.mul_const
    ((n : ℝ) * Real.pi / L))
  simp only [id_eq, Pi.neg_apply, mul_one] at hd
  rw [hd.deriv]
  ring

theorem reflectedCosine_evolution_add (L D : ℝ) (n : ℕ) (s t z : ℝ) :
    Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * (s + t)) *
        Real.cos (((n : ℝ) * Real.pi / L) * z) =
      Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * s) *
        (Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * t) *
          Real.cos (((n : ℝ) * Real.pi / L) * z)) := by
  rw [mul_add, Real.exp_add, mul_assoc]

theorem reflectedCosine_evolution_derivative (L D : ℝ) (n : ℕ) (t z : ℝ) :
    HasDerivAt (fun r : ℝ => Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * r) *
      Real.cos (((n : ℝ) * Real.pi / L) * z))
      (-D * ((n : ℝ) * Real.pi / L) ^ 2 *
        (Real.exp (-D * ((n : ℝ) * Real.pi / L) ^ 2 * t) *
          Real.cos (((n : ℝ) * Real.pi / L) * z))) t := by
  have hd := (((hasDerivAt_id t).const_mul (-D * ((n : ℝ) * Real.pi / L) ^ 2)).exp.mul_const
    (Real.cos (((n : ℝ) * Real.pi / L) * z)))
  simp only [id_eq, mul_one] at hd
  exact hd.congr_deriv (by ring)

end TimeTraps.Probability
