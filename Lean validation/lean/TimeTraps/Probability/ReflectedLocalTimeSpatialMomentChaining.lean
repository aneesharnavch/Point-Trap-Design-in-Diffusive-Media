module

public import TimeTraps.Probability.BrownianDenseContinuityPath

@[expose] public section

/-! Deterministic dyadic chaining in a complete normed space. The input is
only consistency and eventual adjacent-grid bounds; no continuity of the
sampled process is assumed. This applies to continuous-time-path-valued
local time as a process indexed by its spatial level. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal Topology

variable {E : Type*} [NormedAddCommGroup E] [CompleteSpace E]

structure FourthDyadicRegular (v : ℕ → E) : Prop where
  consistent : ∀ i j, brownianDyadicTime i = brownianDyadicTime j → v i = v j
  increments : ∀ R : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ k < R * 64 ^ n,
    dist (v (Nat.pair n (k + 1))) (v (Nat.pair n k)) < (1 / 2 : ℝ) ^ n

noncomputable def fourthDyadicStep (t : ℝ≥0) (n : ℕ) (v : ℕ → E) : E :=
  v (Nat.pair n (brownianDyadicFloor t n))

noncomputable def fourthDyadicPath (t : ℝ≥0) (v : ℕ → E) : E :=
  limUnder atTop (fun n => fourthDyadicStep t n v)

omit [CompleteSpace E] in
theorem fourthDyadicStep_dist_le {ω : ℕ → E}
    (hc : ∀ i j, brownianDyadicTime i = brownianDyadicTime j → ω i = ω j)
    {R n : ℕ} (hi : ∀ k < R * 64 ^ (n + 1),
      dist (ω (Nat.pair (n + 1) (k + 1))) (ω (Nat.pair (n + 1) k)) <
        (1 / 2 : ℝ) ^ (n + 1)) {t : ℝ≥0} (ht : t.val ≤ R) :
    dist (fourthDyadicStep t n ω) (fourthDyadicStep t (n + 1) ω) ≤
      64 * (1 / 2 : ℝ) ^ (n + 1) := by
  have hr := brownianDyadicFloor_refine t n
  have hb := brownianDyadicFloor_le ht (n + 1)
  have he := hc _ _ (brownianDyadicTime_refine n (brownianDyadicFloor t n))
  unfold fourthDyadicStep
  rw [← he]
  calc
    _ ≤ ∑ k ∈ Finset.Ico (64 * brownianDyadicFloor t n) (brownianDyadicFloor t (n + 1)),
        (1 / 2 : ℝ) ^ (n + 1) := by
      apply dist_le_Ico_sum_of_dist_le (f := fun k => ω (Nat.pair (n + 1) k))
        (d := fun _ => (1 / 2 : ℝ) ^ (n + 1)) hr.1
      intro k _ hk
      simpa only [dist_comm] using (hi k (hk.trans_le hb)).le
    _ ≤ 64 * (1 / 2 : ℝ) ^ (n + 1) := by
      simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast (show brownianDyadicFloor t (n + 1) - 64 * brownianDyadicFloor t n ≤ 64
        by omega)

omit [CompleteSpace E] in
theorem FourthDyadicRegular.cauchySeq {ω : ℕ → E} (hω : FourthDyadicRegular ω)
    (t : ℝ≥0) : CauchySeq (fun n => fourthDyadicStep t n ω) := by
  obtain ⟨R, hR⟩ := exists_nat_gt t.val
  obtain ⟨N, hN⟩ := hω.increments R
  apply (cauchySeq_shift N).mp
  apply cauchySeq_of_le_geometric (1 / 2 : ℝ) (64 * (1 / 2 : ℝ) ^ (N + 1))
    (by norm_num)
  intro n
  have h := fourthDyadicStep_dist_le hω.consistent (hN (n + N + 1) (by omega)) hR.le
  simpa only [show n + 1 + N = n + N + 1 by omega,
    show n + N + 1 = N + 1 + n by omega, pow_add, mul_assoc] using h

theorem FourthDyadicRegular.tendsto {ω : ℕ → E} (hω : FourthDyadicRegular ω)
    (t : ℝ≥0) : Tendsto (fun n => fourthDyadicStep t n ω) atTop
      (𝓝 (fourthDyadicPath t ω)) :=
  (hω.cauchySeq t).tendsto_limUnder

end TimeTraps.Probability
