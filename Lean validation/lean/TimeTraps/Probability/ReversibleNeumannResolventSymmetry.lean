module

public import TimeTraps.Probability.ReversibleResistanceNeumannResolvent

@[expose] public section

/-! Original physical Neumann fluxes give the speed-weighted Green
identity and resolvent symmetry. Only the value and flux are
differentiated; the conductance and speed density remain continuous. -/

namespace TimeTraps.Probability

open Set MeasureTheory TimeTraps.Interval

variable {A : IntervalMedium}

theorem ReversibleNeumannTest.generator_integral_zero (H : ReversibleNeumannTest A) :
    (∫ x in A.source.left..A.source.right, A.source.density x * H.generator x) = 0 := by
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le A.source.increasing.le
    H.flux_continuous H.flux_derivative
      ((A.source.continuous.mul H.generator_continuous).intervalIntegrable_of_Icc A.source.increasing.le)
  simpa only [H.neumann_left, H.neumann_right, sub_self] using he

theorem ReversibleNeumannTest.green_identity (H K : ReversibleNeumannTest A) :
    (∫ x in A.source.left..A.source.right, A.source.density x * H.generator x * K.value x) =
      -(∫ x in A.source.left..A.source.right, H.flux x * K.flux x / A.conductance x) := by
  have hi₁ : IntervalIntegrable (fun x => A.source.density x * H.generator x * K.value x)
      volume A.source.left A.source.right :=
    ((A.source.continuous.mul H.generator_continuous).mul K.value_continuous).intervalIntegrable_of_Icc A.source.increasing.le
  have hi₂ : IntervalIntegrable (fun x => H.flux x * K.flux x / A.conductance x)
      volume A.source.left A.source.right :=
    ((H.flux_continuous.mul K.flux_continuous).div A.conductance_continuous
      (fun x hx => (A.conductance_pos x hx).ne')).intervalIntegrable_of_Icc A.source.increasing.le
  have hd (x : ℝ) (hx : x ∈ Ioo A.source.left A.source.right) :
      HasDerivAt (fun y => H.flux y * K.value y)
        (A.source.density x * H.generator x * K.value x + H.flux x * K.flux x / A.conductance x) x := by
    convert! (H.flux_derivative x hx).mul (K.value_derivative x hx) using 1
    ring
  have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le A.source.increasing.le
    (H.flux_continuous.mul K.value_continuous) hd (hi₁.add hi₂)
  rw [intervalIntegral.integral_add hi₁ hi₂] at he
  have hb : H.flux A.source.right * K.value A.source.right -
      H.flux A.source.left * K.value A.source.left = 0 := by
    rw [H.neumann_left, H.neumann_right, zero_mul, zero_mul, sub_self]
  have hz := he.trans hb
  linarith only [hz]

theorem ReversibleNeumannTest.generator_symmetric (H K : ReversibleNeumannTest A) :
    (∫ x in A.source.left..A.source.right, A.source.density x * H.generator x * K.value x) =
      ∫ x in A.source.left..A.source.right, A.source.density x * K.generator x * H.value x := by
  rw [H.green_identity K, K.green_identity H]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [mul_comm (H.flux x) (K.flux x)]

theorem ReversibleNeumannTest.resolvent_symmetric (H K : ReversibleNeumannTest A) (α : ℝ)
    {f g : ℝ → ℝ}
    (hH : ∀ x ∈ Icc A.source.left A.source.right, α * H.value x - H.generator x = f x)
    (hK : ∀ x ∈ Icc A.source.left A.source.right, α * K.value x - K.generator x = g x) :
    (∫ x in A.source.left..A.source.right, A.source.density x * f x * K.value x) =
      ∫ x in A.source.left..A.source.right, A.source.density x * g x * H.value x := by
  have hmass : IntervalIntegrable (fun x => α * (A.source.density x * H.value x * K.value x))
      volume A.source.left A.source.right :=
    ((A.source.continuous.mul H.value_continuous).mul K.value_continuous).intervalIntegrable_of_Icc A.source.increasing.le |>.const_mul α
  have hiH : IntervalIntegrable (fun x => A.source.density x * H.generator x * K.value x)
      volume A.source.left A.source.right :=
    ((A.source.continuous.mul H.generator_continuous).mul K.value_continuous).intervalIntegrable_of_Icc A.source.increasing.le
  have hiK : IntervalIntegrable (fun x => A.source.density x * K.generator x * H.value x)
      volume A.source.left A.source.right :=
    ((A.source.continuous.mul K.generator_continuous).mul H.value_continuous).intervalIntegrable_of_Icc A.source.increasing.le
  have heH : EqOn (fun x => A.source.density x * f x * K.value x)
      (fun x => α * (A.source.density x * H.value x * K.value x) - A.source.density x * H.generator x * K.value x)
        (Icc A.source.left A.source.right) := by
    intro x hx
    dsimp only
    rw [← hH x hx]
    ring
  have heK : EqOn (fun x => A.source.density x * g x * H.value x)
      (fun x => α * (A.source.density x * H.value x * K.value x) - A.source.density x * K.generator x * H.value x)
        (Icc A.source.left A.source.right) := by
    intro x hx
    dsimp only
    rw [← hK x hx]
    ring
  rw [intervalIntegral.integral_congr (fun x hx => heH (uIcc_of_le A.source.increasing.le ▸ hx)),
    intervalIntegral.integral_congr (fun x hx => heK (uIcc_of_le A.source.increasing.le ▸ hx)),
    intervalIntegral.integral_sub hmass hiH, intervalIntegral.integral_sub hmass hiK, H.generator_symmetric K]

theorem ReversibleNeumannTest.resolvent_mass (H : ReversibleNeumannTest A) (α : ℝ)
    {f : ℝ → ℝ}
    (hH : ∀ x ∈ Icc A.source.left A.source.right, α * H.value x - H.generator x = f x) :
    (∫ x in A.source.left..A.source.right, A.source.density x * f x) =
      α * ∫ x in A.source.left..A.source.right, A.source.density x * H.value x := by
  have hi : IntervalIntegrable (fun x => A.source.density x * H.value x)
      volume A.source.left A.source.right :=
    (A.source.continuous.mul H.value_continuous).intervalIntegrable_of_Icc A.source.increasing.le
  have hg : IntervalIntegrable (fun x => A.source.density x * H.generator x)
      volume A.source.left A.source.right :=
    (A.source.continuous.mul H.generator_continuous).intervalIntegrable_of_Icc A.source.increasing.le
  calc
    _ = ∫ x in A.source.left..A.source.right,
        α * (A.source.density x * H.value x) - A.source.density x * H.generator x := by
      apply intervalIntegral.integral_congr
      intro x hx
      dsimp only
      rw [← hH x (uIcc_of_le A.source.increasing.le ▸ hx)]
      ring
    _ = _ := by rw [intervalIntegral.integral_sub (hi.const_mul α) hg,
      intervalIntegral.integral_const_mul, H.generator_integral_zero, sub_zero]

end TimeTraps.Probability
