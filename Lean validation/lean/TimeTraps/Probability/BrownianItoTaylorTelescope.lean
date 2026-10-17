module

public import TimeTraps.Probability.BrownianItoTaylorSum
public import TimeTraps.Probability.BrownianItoDriftStep
public import TimeTraps.Probability.BrownianWeightedQuadraticFunction

@[expose] public section

/-! Exact finite Taylor telescoping and the separation of its second-order
term into ordinary drift and compensated quadratic variation. -/

namespace TimeTraps.Probability

open TimeTraps.Analysis
open scoped NNReal

theorem ito_finite_differences {N : ℕ} (a : Fin (N + 1) → ℝ) :
    (∑ i : Fin N, (a i.succ - a i.castSucc)) = a (Fin.last N) - a 0 := by
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ a
  have h₂ := Fin.sum_univ_castSucc a
  linarith

theorem ito_finite_taylor (F : ℝ → ℝ) {N : ℕ} (x : Fin (N + 1) → ℝ) :
    F (x (Fin.last N)) - F (x 0) =
      (∑ i : Fin N, deriv F (x i.castSucc) * (x i.succ - x i.castSucc)) +
      (1 / 2 : ℝ) * (∑ i : Fin N, deriv (deriv F) (x i.castSucc) * (x i.succ - x i.castSucc) ^ 2) +
      ∑ i : Fin N, itoTaylorRemainder F (x i.castSucc) (x i.succ) := by
  rw [← ito_finite_differences (fun i => F (x i)), Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  unfold itoTaylorRemainder
  ring

theorem brownianItoTaylorDyadic_telescope {Ω : Type*} (B : ℝ≥0 → Ω → ℝ)
    (F : ℝ → ℝ) (T : ℝ≥0) (n : ℕ) (ω : Ω) :
    F (B T ω) - F (B 0 ω) =
      (∑ i : Fin (2 ^ n), deriv F (B (brownianDyadicGrid T n i.castSucc) ω) *
        (B (brownianDyadicGrid T n i.succ) ω - B (brownianDyadicGrid T n i.castSucc) ω)) +
      (1 / 2 : ℝ) * brownianItoDriftSum B (deriv (deriv F)) T n ω +
      (1 / 2 : ℝ) * brownianWeightedDyadicFunction B (deriv (deriv F)) T n ω +
      brownianItoTaylorSum B F (brownianDyadicGrid T n) ω := by
  have h₀ : brownianDyadicGrid T n 0 = 0 := by simp [brownianDyadicGrid]
  have hT : brownianDyadicGrid T n (Fin.last (2 ^ n)) = T := by
    apply Subtype.ext
    change ((2 ^ n : ℕ) : ℝ) * T.val / (2 : ℝ) ^ n = T.val
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    field_simp
  have he := ito_finite_taylor F (fun i : Fin (2 ^ n + 1) => B (brownianDyadicGrid T n i) ω)
  rw [h₀, hT] at he
  have hs : (∑ i : Fin (2 ^ n), deriv (deriv F) (B (brownianDyadicGrid T n i.castSucc) ω) *
      (B (brownianDyadicGrid T n i.succ) ω - B (brownianDyadicGrid T n i.castSucc) ω) ^ 2) =
      brownianItoDriftSum B (deriv (deriv F)) T n ω +
        brownianWeightedDyadicFunction B (deriv (deriv F)) T n ω := by
    unfold brownianItoDriftSum brownianWeightedDyadicFunction brownianWeightedDyadicQuadratic
      brownianWeightedQuadraticSum brownianCompensatedSquareIncrement
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  change F (B T ω) - F (B 0 ω) = _ at he
  rw [hs] at he
  change F (B T ω) - F (B 0 ω) = _
  unfold brownianItoTaylorSum brownianItoTaylorIncrement
  linarith

end TimeTraps.Probability
