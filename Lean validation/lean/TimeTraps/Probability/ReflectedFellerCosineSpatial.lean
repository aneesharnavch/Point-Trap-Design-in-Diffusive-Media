module

public import TimeTraps.Probability.ReflectedFellerCosineCore
public import TimeTraps.Probability.ReflectedFoldCosineEvolution

@[expose] public section

/-! The finite-span Feller derivative is literally `D` times the classical
second derivative of the finite cosine polynomial, whose two endpoint
derivatives vanish. No converse generator-domain statement is asserted. -/

namespace TimeTraps.Probability

open Set TimeTraps.Analysis

noncomputable def reflectedCosinePolynomial (L : ℝ) (s : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) : ℝ :=
  ∑ n ∈ s, c n * Real.cos (((n : ℝ) * Real.pi / L) * x)

theorem reflectedCosinePolynomial_derivative (L : ℝ) (s : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) :
    HasDerivAt (reflectedCosinePolynomial L s c)
      (∑ n ∈ s, c n * (-Real.sin (((n : ℝ) * Real.pi / L) * x) * ((n : ℝ) * Real.pi / L))) x := by
  exact HasDerivAt.fun_sum (fun n (_ : n ∈ s) => (reflectedCosine_derivative L n x).const_mul (c n))

theorem reflectedCosinePolynomial_second (L D : ℝ) (s : Finset ℕ) (c : ℕ → ℝ) (x : ℝ) :
    D * deriv (deriv (reflectedCosinePolynomial L s c)) x =
      ∑ n ∈ s, (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) *
        Real.cos (((n : ℝ) * Real.pi / L) * x) := by
  have hf : deriv (reflectedCosinePolynomial L s c) =
      (fun y => ∑ n ∈ s, c n * (-Real.sin (((n : ℝ) * Real.pi / L) * y) *
        ((n : ℝ) * Real.pi / L))) :=
    funext (fun y => (reflectedCosinePolynomial_derivative L s c y).deriv)
  rw [hf]
  have hd (n : ℕ) : HasDerivAt
      (fun y : ℝ => c n * (-Real.sin (((n : ℝ) * Real.pi / L) * y) * ((n : ℝ) * Real.pi / L)))
      (c n * (-(Real.cos (((n : ℝ) * Real.pi / L) * x) * ((n : ℝ) * Real.pi / L)) *
        ((n : ℝ) * Real.pi / L))) x := by
    simpa only [id_eq, Pi.neg_apply, mul_one] using
      (((((hasDerivAt_id x).const_mul ((n : ℝ) * Real.pi / L)).sin).neg.mul_const
        ((n : ℝ) * Real.pi / L)).const_mul (c n))
  rw [(HasDerivAt.fun_sum (fun n (_ : n ∈ s) => hd n)).deriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem reflectedCosinePolynomial_neumann (L : ℝ) (hL : 0 < L) (s : Finset ℕ) (c : ℕ → ℝ) :
    deriv (reflectedCosinePolynomial L s c) 0 = 0 ∧
      deriv (reflectedCosinePolynomial L s c) L = 0 := by
  constructor
  · rw [(reflectedCosinePolynomial_derivative L s c 0).deriv]
    simp
  · rw [(reflectedCosinePolynomial_derivative L s c L).deriv]
    simp only [div_mul_cancel₀ _ hL.ne', Real.sin_nat_mul_pi, neg_zero, zero_mul, mul_zero,
      Finset.sum_const_zero]

theorem reflectedFellerOperator_finite_spatial_generator (L : ℝ) (hL : 0 < L)
    (D : ℝ) (hD : 0 ≤ D) (s : Finset ℕ) (c : ℕ → ℝ) :
    ∃ g : C(Icc (0 : ℝ) L, ℝ),
      HasDerivWithinAt (fun t : ℝ => reflectedFellerOperator L hL (Real.toNNReal (2 * D * t))
        (∑ n ∈ s, c n • neumannCosine L n)) g (Ici 0) 0 ∧
      ∀ x : Icc (0 : ℝ) L, g x = D * deriv (deriv (reflectedCosinePolynomial L s c)) x.val := by
  refine ⟨∑ n ∈ s, (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) • neumannCosine L n,
    reflectedFellerOperator_finite_cosine_generator L hL D hD s c, ?_⟩
  intro x
  rw [reflectedCosinePolynomial_second]
  simp only [ContinuousMap.sum_apply, ContinuousMap.smul_apply, smul_eq_mul,
    neumannCosine, Int.cast_natCast, ContinuousMap.coe_mk]

end TimeTraps.Probability
