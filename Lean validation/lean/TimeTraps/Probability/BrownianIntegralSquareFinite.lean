module

public import TimeTraps.Probability.BrownianIntegralRepresentation
public import TimeTraps.Probability.BrownianQuadraticVariation

@[expose] public section

/-! The exact finite algebra behind the quadratic Ito identity, and the
actual elementary adapted integrands on the dyadic partition of [0,T]. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem brownianSquare_telescope {N : ℕ} (u : Fin (N + 1) → ℝ) :
    2 * (∑ i : Fin N, u i.castSucc * (u i.succ - u i.castSucc)) +
      ∑ i : Fin N, (u i.succ - u i.castSucc) ^ 2 = u (Fin.last N) ^ 2 - u 0 ^ 2 := by
  have htel : (∑ i : Fin N, (u i.succ ^ 2 - u i.castSucc ^ 2)) =
      u (Fin.last N) ^ 2 - u 0 ^ 2 := by
    rw [Finset.sum_sub_distrib]
    have h₁ := Fin.sum_univ_succ (fun i : Fin (N + 1) => u i ^ 2)
    have h₂ := Fin.sum_univ_castSucc (fun i : Fin (N + 1) => u i ^ 2)
    linarith
  rw [← htel, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem brownianDyadicGrid_zero (T : ℝ≥0) (n : ℕ) : brownianDyadicGrid T n 0 = 0 := by
  simp [brownianDyadicGrid]

theorem brownianDyadicGrid_last (T : ℝ≥0) (n : ℕ) :
    brownianDyadicGrid T n (Fin.last (2 ^ n)) = T := by
  simp only [brownianDyadicGrid, Fin.val_last, Nat.cast_pow, Nat.cast_ofNat]
  field_simp

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

noncomputable def brownianSquareElementary (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) (i : Fin (2 ^ n)) :
    BrownianIntegralElementary B hBm P where
  left := brownianDyadicGrid T n i.castSucc
  right := brownianDyadicGrid T n i.succ
  ordered := brownianDyadicGrid_monotone T n (Fin.castSucc_le_succ i)
  coefficient := B (brownianDyadicGrid T n i.castSucc)
  adapted := brownianNaturalFiltration_stronglyAdapted B hBm _
  squareIntegrable := (hB.hasLaw_eval _).hasGaussianLaw.memLp_two

noncomputable def brownianSquareStepIntegrand (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) : brownianIntegralSpace B hBm P :=
  brownianElementarySumIntegrand (brownianSquareElementary hB hBm T n)

/-- Every finite dyadic stochastic sum equals half the terminal square
minus the actual finite quadratic variation. -/
theorem brownianSquareStep_integral_ae (hB : IsPreBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) (T : ℝ≥0) (n : ℕ) :
    brownianIntegral hB (brownianSquareStepIntegrand hB hBm T n) =ᵐ[P]
      fun ω => (B T ω ^ 2 - brownianDyadicQV B T n ω) / 2 := by
  have he := brownianIntegral_elementarySum_ae hB (brownianSquareElementary hB hBm T n)
  filter_upwards [he, hB.eval_zero_ae_eq_zero] with ω hω hzero
  change (brownianIntegral hB (brownianElementarySumIntegrand
    (brownianSquareElementary hB hBm T n))) ω = _
  rw [hω]
  have ht := brownianSquare_telescope (fun i => B (brownianDyadicGrid T n i) ω)
  rw [brownianDyadicGrid_zero, brownianDyadicGrid_last, hzero, zero_pow (by norm_num), sub_zero] at ht
  change (∑ i : Fin (2 ^ n), B (brownianDyadicGrid T n i.castSucc) ω *
    (B (brownianDyadicGrid T n i.succ) ω - B (brownianDyadicGrid T n i.castSucc) ω)) = _
  change 2 * (∑ i : Fin (2 ^ n), B (brownianDyadicGrid T n i.castSucc) ω *
    (B (brownianDyadicGrid T n i.succ) ω - B (brownianDyadicGrid T n i.castSucc) ω)) +
      brownianDyadicQV B T n ω = B T ω ^ 2 at ht
  linarith

end TimeTraps.Probability
