module

public import TimeTraps.Probability.ReflectedFellerPrimitive

@[expose] public section

/-! Exact integration of nonconstant Neumann modes. In particular, mean
removal eliminates the constant mode, and double integration of every
other mode is a finite cosine polynomial. -/

noncomputable section

namespace TimeTraps.Probability

open MeasureTheory Set TimeTraps.Analysis

theorem reflectedFeller_cosine_frequency_ne (L : ℝ) (hL : 0 < L)
    (n : ℕ) (hn : n ≠ 0) : (n : ℝ) * Real.pi / L ≠ 0 :=
  div_ne_zero (mul_ne_zero (Nat.cast_ne_zero.mpr hn) Real.pi_ne_zero) hL.ne'

theorem reflectedFellerPrimitive_cosine (L : ℝ) (hL : 0 < L)
    (n : ℕ) (hn : n ≠ 0) (x : Icc (0 : ℝ) L) :
    reflectedFellerPrimitive L hL (neumannCosine L n) x =
      Real.sin (((n : ℝ) * Real.pi / L) * x.val) / ((n : ℝ) * Real.pi / L) := by
  let a := (n : ℝ) * Real.pi / L
  have ha : a ≠ 0 := reflectedFeller_cosine_frequency_ne L hL n hn
  have he := reflectedFellerPrimitive_of_derivative L hL (neumannCosine L n)
    (fun y => Real.sin (a * y) / a) (by fun_prop) (fun y _ => by
      rw [reflectedFellerExtension_cosine]
      have hd := (((hasDerivAt_id y).const_mul a).sin).div_const a
      simp only [id_eq, mul_one] at hd
      apply hd.congr_deriv
      dsimp [a]
      field_simp) x
  simpa only [mul_zero, Real.sin_zero, zero_div, sub_zero] using he

theorem reflectedFellerMean_cosine (L : ℝ) (hL : 0 < L)
    (n : ℕ) (hn : n ≠ 0) : reflectedFellerMean L hL (neumannCosine L n) = 0 := by
  change L⁻¹ * reflectedFellerPrimitive L hL (neumannCosine L n) ⟨L, hL.le, le_rfl⟩ = 0
  rw [reflectedFellerPrimitive_cosine L hL n hn]
  simp only [div_mul_cancel₀ _ hL.ne', Real.sin_nat_mul_pi, zero_div, mul_zero]

theorem reflectedFellerMeanZero_cosine (L : ℝ) (hL : 0 < L)
    (n : ℕ) (hn : n ≠ 0) :
    reflectedFellerMeanZero L hL (neumannCosine L n) = neumannCosine L n := by
  rw [reflectedFellerMeanZero_apply, reflectedFellerMean_cosine L hL n hn, zero_smul, sub_zero]

theorem reflectedFellerPrimitive_twice_cosine (L : ℝ) (hL : 0 < L)
    (n : ℕ) (hn : n ≠ 0) :
    reflectedFellerPrimitive L hL (reflectedFellerPrimitive L hL (neumannCosine L n)) =
      (((n : ℝ) * Real.pi / L) ^ 2)⁻¹ • (1 - neumannCosine L n) := by
  let a := (n : ℝ) * Real.pi / L
  have ha : a ≠ 0 := reflectedFeller_cosine_frequency_ne L hL n hn
  ext x
  have he := reflectedFellerPrimitive_of_derivative L hL
    (reflectedFellerPrimitive L hL (neumannCosine L n))
    (fun y => (1 - Real.cos (a * y)) / a ^ 2) (by fun_prop) (fun y hy => by
      rw [reflectedFellerExtension_on_interval L hL _ ⟨y, hy.1.le, hy.2.le⟩,
        reflectedFellerPrimitive_cosine L hL n hn]
      have hd := ((hasDerivAt_const y (1 : ℝ)).sub
        (((hasDerivAt_id y).const_mul a).cos)).div_const (a ^ 2)
      simp only [id_eq, mul_one, zero_sub] at hd
      apply hd.congr_deriv
      change -(-Real.sin (a * y) * a) / a ^ 2 = Real.sin (a * y) / a
      field_simp) x
  simpa only [a, mul_zero, Real.cos_zero, sub_self, zero_div, sub_zero,
    ContinuousMap.smul_apply, ContinuousMap.sub_apply, ContinuousMap.one_apply,
    neumannCosine, ContinuousMap.coe_mk, Int.cast_natCast, smul_eq_mul,
    div_eq_mul_inv, mul_comm] using he

end TimeTraps.Probability

end
