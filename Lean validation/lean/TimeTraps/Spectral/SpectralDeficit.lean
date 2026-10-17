module

public import TimeTraps.Spectral.TangentConvexity
public import TimeTraps.Spectral.TangentJump
public import TimeTraps.Spectral.PhaseEquality

@[expose] public section

/-! Exact nonnegative phase losses for actual physical positive eigenstates. -/

namespace TimeTraps.Spectral

open Set
open scoped BigOperators

variable {n : ℕ} {P : SpectralProblem n} {ev k : ℝ}

noncomputable def PositiveEigenstate.phaseDelta (E : PositiveEigenstate P ev)
    (k : ℝ) (i : Fin n) : ℝ :=
  E.phase k i.succ 0 - E.phase k i.castSucc (P.shooting.gap i.castSucc)

noncomputable def PositiveEigenstate.localTangentLoss (E : PositiveEigenstate P ev)
    (k : ℝ) (i : Fin n) : ℝ :=
  Real.tan (E.phase k i.succ 0) -
    Real.tan (E.phase k i.castSucc (P.shooting.gap i.castSucc)) -
      2 * tangentHalf (E.phaseDelta k i)

noncomputable def PositiveEigenstate.allocationLoss (E : PositiveEigenstate P ev)
    (k : ℝ) : ℝ :=
  2 * ((∑ i, tangentHalf (E.phaseDelta k i)) -
    n * Real.tan (k * P.length / (2 * n)))

noncomputable def SpectralProblem.spectralDeficit (P : SpectralProblem n) (k : ℝ) : ℝ :=
  (∑ i, P.strength i) / (P.diffusivity * k) -
    2 * n * Real.tan (k * P.length / (2 * n))

theorem PositiveEigenstate.phaseDelta_mem (E : PositiveEigenstate P ev)
    (hk : 0 < k) (i : Fin n) : E.phaseDelta k i ∈ Ioo 0 Real.pi :=
  positive_phase_difference_mem
    (div_pos (P.strength_pos i) (mul_pos P.diffusivity_pos hk))
    (E.phase_branch k i.castSucc (P.shooting.gap i.castSucc))
    (E.phase_branch k i.succ 0) (E.phase_tan_jump hk i)

theorem PositiveEigenstate.phaseDelta_sum (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    (∑ i, E.phaseDelta k i) = k * P.length := (E.phase_sum hk hk2).symm

theorem PositiveEigenstate.mean_phase_mem (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    k * P.length / (2 * n) ∈ Ioo 0 (Real.pi / 2) := by
  have hn : (0 : ℝ) < n := Nat.cast_pos.mpr P.count_pos
  have hs : (∑ i, E.phaseDelta k i) < ∑ _i : Fin n, Real.pi :=
    Finset.sum_lt_sum_of_nonempty ⟨⟨0, P.count_pos⟩, Finset.mem_univ _⟩
      (fun i _ => (E.phaseDelta_mem hk i).2)
  rw [E.phaseDelta_sum hk hk2] at hs
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
  refine ⟨div_pos (mul_pos hk P.length_pos) (by positivity), ?_⟩
  apply (div_lt_iff₀ (show (0 : ℝ) < 2 * n by positivity)).mpr
  nlinarith

theorem PositiveEigenstate.localTangentLoss_nonneg (E : PositiveEigenstate P ev)
    (hk : 0 < k) (i : Fin n) : 0 ≤ E.localTangentLoss k i := by
  have h := (sharp_tangent_jump
    (div_pos (P.strength_pos i) (mul_pos P.diffusivity_pos hk))
    (E.phase_branch k i.castSucc (P.shooting.gap i.castSucc))
    (E.phase_branch k i.succ 0) (E.phase_tan_jump hk i)).1
  unfold localTangentLoss tangentHalf phaseDelta
  rw [E.phase_tan_jump hk i]
  exact sub_nonneg.mpr h

theorem PositiveEigenstate.localTangentLoss_eq_zero_iff (E : PositiveEigenstate P ev)
    (hk : 0 < k) (i : Fin n) :
    E.localTangentLoss k i = 0 ↔
      E.phase k i.succ 0 = -E.phase k i.castSucc (P.shooting.gap i.castSucc) := by
  have h := (sharp_tangent_jump
    (div_pos (P.strength_pos i) (mul_pos P.diffusivity_pos hk))
    (E.phase_branch k i.castSucc (P.shooting.gap i.castSucc))
    (E.phase_branch k i.succ 0) (E.phase_tan_jump hk i)).2
  unfold localTangentLoss tangentHalf phaseDelta
  rw [E.phase_tan_jump hk i, sub_eq_zero, eq_comm]
  exact h

theorem PositiveEigenstate.allocationLoss_nonneg (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) : 0 ≤ E.allocationLoss k := by
  have h := tangentHalf_sum_ge P.count_pos (E.phaseDelta k) (E.phaseDelta_mem hk)
  rw [E.phaseDelta_sum hk hk2] at h
  have hm : tangentHalf (k * P.length / n) = Real.tan (k * P.length / (2 * n)) := by
    unfold tangentHalf
    congr 1
    ring
  rw [hm] at h
  exact mul_nonneg (by norm_num) (sub_nonneg.mpr h)

theorem PositiveEigenstate.allocationLoss_eq_zero_iff (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    E.allocationLoss k = 0 ↔ ∀ i, E.phaseDelta k i = k * P.length / n := by
  have h := tangentHalf_sum_eq_iff P.count_pos (E.phaseDelta k) (E.phaseDelta_mem hk)
  rw [E.phaseDelta_sum hk hk2] at h
  have hm : tangentHalf (k * P.length / n) = Real.tan (k * P.length / (2 * n)) := by
    unfold tangentHalf
    congr 1
    ring
  rw [hm] at h
  unfold allocationLoss
  rw [mul_eq_zero, or_iff_right (by norm_num : (2 : ℝ) ≠ 0), sub_eq_zero]
  exact h

theorem PositiveEigenstate.spectral_deficit_identity (E : PositiveEigenstate P ev)
    (hk : 0 < k) :
    P.spectralDeficit k = (∑ i, E.localTangentLoss k i) + E.allocationLoss k := by
  have hs : (∑ i : Fin n, (Real.tan (E.phase k i.succ 0) -
      Real.tan (E.phase k i.castSucc (P.shooting.gap i.castSucc)))) =
      (∑ i, P.strength i) / (P.diffusivity * k) := by
    simp_rw [E.phase_tan_jump hk]
    exact (Finset.sum_div _ _ _).symm
  unfold SpectralProblem.spectralDeficit localTangentLoss allocationLoss
  rw [Finset.sum_sub_distrib, hs, ← Finset.mul_sum]
  ring

theorem PositiveEigenstate.spectral_deficit_nonneg (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) : 0 ≤ P.spectralDeficit k := by
  rw [E.spectral_deficit_identity hk]
  exact add_nonneg (Finset.sum_nonneg fun i _ => E.localTangentLoss_nonneg hk i)
    (E.allocationLoss_nonneg hk hk2)

theorem PositiveEigenstate.spectral_deficit_eq_zero_iff (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    P.spectralDeficit k = 0 ↔
      (∀ i : Fin n, E.phase k i.succ 0 = -E.phase k i.castSucc (P.shooting.gap i.castSucc)) ∧
      (∀ i, E.phaseDelta k i = k * P.length / n) := by
  rw [E.spectral_deficit_identity hk]
  rw [add_eq_zero_iff_of_nonneg
    (Finset.sum_nonneg fun i _ => E.localTangentLoss_nonneg hk i)
    (E.allocationLoss_nonneg hk hk2)]
  rw [Finset.sum_eq_zero_iff_of_nonneg (fun i _ => E.localTangentLoss_nonneg hk i)]
  simp only [Finset.mem_univ, forall_true_left, E.localTangentLoss_eq_zero_iff hk,
    E.allocationLoss_eq_zero_iff hk hk2]

theorem PositiveEigenstate.prescribed_deficit_identity (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    2 * (∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k))) - k * P.length =
      ∑ i, (2 * Real.arctan (P.strength i / (2 * P.diffusivity * k)) - E.phaseDelta k i) := by
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, E.phaseDelta_sum hk hk2]

theorem PositiveEigenstate.prescribed_deficit_nonneg (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    0 ≤ 2 * (∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k))) - k * P.length := by
  have h := E.phase_global_bound hk hk2
  rw [mul_comm P.length] at h
  exact sub_nonneg.mpr h

theorem PositiveEigenstate.prescribed_deficit_eq_zero_iff (E : PositiveEigenstate P ev)
    (hk : 0 < k) (hk2 : k ^ 2 = ev / P.diffusivity) :
    2 * (∑ i, Real.arctan (P.strength i / (2 * P.diffusivity * k))) - k * P.length = 0 ↔
      ∀ i : Fin n, E.phase k i.succ 0 = -E.phase k i.castSucc (P.shooting.gap i.castSucc) := by
  rw [sub_eq_zero, eq_comm, mul_comm k]
  exact E.phase_global_eq_iff hk hk2

end TimeTraps.Spectral
