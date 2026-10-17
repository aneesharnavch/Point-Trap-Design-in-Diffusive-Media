module

public import TimeTraps.Probability.ReflectedCosineDynkinMartingale
public import TimeTraps.Probability.ReflectedFellerCosineSpatial

@[expose] public section

/-! Actual Dynkin martingales for finite Neumann cosine polynomials.
Finite time-integral linearity is justified by bounded measurable
integrands. Signed coefficients, the empty sum, and the constant mode
are included. All representative identities are fixed-time a.e. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem reflectedCosineDynkin_sum_physical
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ≥0) (ω : Ω) :
    (∑ n ∈ s, c n * reflectedCosineDynkin B L D x n t ω) =
      reflectedCosinePolynomial L s c (foldedTrajectory L D x B t ω) -
        reflectedCosinePolynomial L s c (foldedTrajectory L D x B 0 ω) -
      D * (∫ r in (0 : ℝ)..t.val, deriv (deriv (reflectedCosinePolynomial L s c))
        (foldedTrajectory L D x B r.toNNReal ω)) := by
  have hi : D * (∫ r in (0 : ℝ)..t.val, deriv (deriv (reflectedCosinePolynomial L s c))
      (foldedTrajectory L D x B r.toNNReal ω)) =
      ∑ n ∈ s, (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) *
        brownianItoDrift B (reflectedCosineInput L D x n) t ω := by
    have he : (fun r : ℝ => D * deriv (deriv (reflectedCosinePolynomial L s c))
        (foldedTrajectory L D x B r.toNNReal ω)) =
        (fun r : ℝ => ∑ n ∈ s, (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) *
          reflectedCosineInput L D x n (B r.toNNReal ω)) := by
      funext r
      rw [reflectedCosinePolynomial_second]
      apply Finset.sum_congr rfl
      intro n _
      rw [reflectedCosineInput_folded L hL]
    rw [← intervalIntegral.integral_const_mul, he]
    rw [intervalIntegral.integral_finsetSum (fun n _ =>
      (brownianItoDrift_bounded_intervalIntegrable
        (reflectedCosineInput_lipschitz L D x n).continuous.measurable hjoint
        (reflectedCosineInput_bound L D x n) t ω).const_mul (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)))]
    simp only [intervalIntegral.integral_const_mul, brownianItoDrift]
  calc
    _ = ∑ n ∈ s, (c n * reflectedCosineInput L D x n (B t ω) -
        c n * reflectedCosineInput L D x n (B 0 ω) -
        (c n * (-D * ((n : ℝ) * Real.pi / L) ^ 2)) *
          brownianItoDrift B (reflectedCosineInput L D x n) t ω) := by
      apply Finset.sum_congr rfl
      intro n _
      unfold reflectedCosineDynkin
      ring
    _ = _ := by
      rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, hi]
      simp only [reflectedCosinePolynomial, reflectedCosineInput_folded L hL]

noncomputable def reflectedCosinePolynomialDynkinVersion (B : ℝ≥0 → Ω → ℝ)
    (hBm : ∀ t, Measurable (B t)) (P : Measure Ω) (L D x : ℝ)
    (s : Finset ℕ) (c : ℕ → ℝ) : ℝ≥0 → Ω → ℝ :=
  ∑ n ∈ s, c n • reflectedCosineDynkinVersion B hBm P L D x n

theorem reflectedCosinePolynomialDynkinVersion_martingale (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (s : Finset ℕ) (c : ℕ → ℝ) :
    Martingale (reflectedCosinePolynomialDynkinVersion B hBm P L D x s c)
      (brownianNaturalFiltration B hBm) P := by
  classical
  unfold reflectedCosinePolynomialDynkinVersion
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using martingale_zero ℝ (brownianNaturalFiltration B hBm) P
  | @insert n s hns ih =>
    rw [Finset.sum_insert hns]
    exact ((reflectedCosineDynkinVersion_martingale hB hBm hjoint L hL D hD x n).smul (c n)).add ih

theorem reflectedCosinePolynomialDynkinVersion_physical_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t))
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2))
    (L : ℝ) (hL : 0 < L) (D x : ℝ) (s : Finset ℕ) (c : ℕ → ℝ) (t : ℝ≥0) :
    reflectedCosinePolynomialDynkinVersion B hBm P L D x s c t =ᵐ[P] (fun ω =>
      reflectedCosinePolynomial L s c (foldedTrajectory L D x B t ω) -
        reflectedCosinePolynomial L s c (foldedTrajectory L D x B 0 ω) -
      D * (∫ r in (0 : ℝ)..t.val, deriv (deriv (reflectedCosinePolynomial L s c))
        (foldedTrajectory L D x B r.toNNReal ω))) := by
  filter_upwards [ae_all_iff.mpr (fun n => reflectedCosineDynkinVersion_ae hB hBm hjoint L D x n t)]
    with ω hω
  unfold reflectedCosinePolynomialDynkinVersion
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  calc
    _ = ∑ n ∈ s, c n * reflectedCosineDynkin B L D x n t ω := by
      apply Finset.sum_congr rfl
      intro n _
      rw [hω n]
    _ = _ := reflectedCosineDynkin_sum_physical hjoint L hL D x s c t ω

theorem brownianDyadic_reflectedCosinePolynomial_dynkin_martingale
    (L : ℝ) (hL : 0 < L) (D : ℝ) (hD : 0 < D) (x : ℝ) (s : Finset ℕ) (c : ℕ → ℝ) :
    Martingale (reflectedCosinePolynomialDynkinVersion brownianDyadicPath brownianDyadicPath_measurable
      brownianDyadicMeasure L D x s c) brownianFiltration brownianDyadicMeasure :=
  reflectedCosinePolynomialDynkinVersion_martingale brownianDyadicPath_isPreBrownianReal
    brownianDyadicPath_measurable brownianDyadicPath_jointly_measurable L hL D hD x s c

end TimeTraps.Probability
