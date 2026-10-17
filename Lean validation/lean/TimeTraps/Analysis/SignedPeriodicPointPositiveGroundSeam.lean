module

public import TimeTraps.Analysis.SignedPeriodicPointPositiveGroundInterior
public import TimeTraps.Analysis.IntervalEndpointMinimumDerivative

@[expose] public section

/-! A nonnegative periodic state vanishing at the seam has inward slopes
of opposite sign. The signed seam equation makes them equal, hence zero.
Linear Cauchy uniqueness then forces the whole state to vanish. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ}
variable {P : SignedPeriodicPointProblem ι l r} {n : ℕ}

theorem SignedPeriodicPointPartition.seam_zero_slopes
    (Q : SignedPeriodicPointPartition P n) {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ}
    {c : ℝ}
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => c * u x)
      (Q.point e.castSucc) (Q.point e.succ))
    (ht : SignedPeriodicPointTransmission Q u j)
    (hn : ∀ x ∈ Icc l r, 0 ≤ u x) (hz : u l = 0) :
    j 0 l = 0 ∧ j (Fin.last n) r = 0 := by
  have hc (e : Fin (n + 1)) : ContinuousOn (j e)
      (Icc (Q.point e.castSucc) (Q.point e.succ)) := by
    simpa only [uIcc_of_le (Q.strictMono Fin.castSucc_lt_succ).le] using
      (hj e).slope_energy.continuousOn
  have hd₀ : HasDerivWithinAt u (j 0 l) (Ici l) l := by
    simpa only [Fin.castSucc_zero, Q.left_eq] using
      intervalEnergy_hasDerivWithinAt_left_of_ae_deriv (hj 0).state_energy
        (Q.strictMono Fin.castSucc_lt_succ) (hc 0) (hj 0).slope_ae
  have hd₁ : HasDerivWithinAt u (j (Fin.last n) r) (Iic r) r := by
    simpa only [Fin.succ_last, Q.right_eq] using
      intervalEnergy_hasDerivWithinAt_right_of_ae_deriv (hj (Fin.last n)).state_energy
        (Q.strictMono Fin.castSucc_lt_succ) (hc (Fin.last n)) (hj (Fin.last n)).slope_ae
  have hr : u r = 0 := ht.periodic_state.symm.trans hz
  have h₀ := interval_nonnegative_left_derivative P.boundary.interval_pos hn hz hd₀
  have h₁ := interval_nonnegative_right_derivative P.boundary.interval_pos hn hr hd₁
  have he := ht.seam_jump
  rw [hz, mul_zero] at he
  have heq : j 0 l = j (Fin.last n) r :=
    sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left P.diffusivity_pos.ne')
  constructor <;> linarith

theorem SignedPeriodicPointPartition.eq_zero_of_nonnegative_seam_zero
    (Q : SignedPeriodicPointPartition P n) {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ}
    {c : ℝ}
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => c * u x)
      (Q.point e.castSucc) (Q.point e.succ))
    (ht : SignedPeriodicPointTransmission Q u j)
    (hn : ∀ x ∈ Icc l r, 0 ≤ u x) (hz : u l = 0) :
    ∀ x ∈ Icc l r, u x = 0 := by
  have hs := (Q.seam_zero_slopes hj ht hn hz).1
  have hzu : u (Q.point (0 : Fin (n + 1)).castSucc) = 0 := by
    simpa only [Fin.castSucc_zero, Q.left_eq] using hz
  have hzj : j 0 (Q.point (0 : Fin (n + 1)).castSucc) = 0 := by
    simpa only [Fin.castSucc_zero, Q.left_eq] using hs
  have hcell := (hj 0).eq_zero_of_linear_cauchy (Q.strictMono Fin.castSucc_lt_succ)
    ⟨le_rfl, (Q.strictMono Fin.castSucc_lt_succ).le⟩ hzu hzj
  have hall := Q.all_cells_zero_of_cell_zero hj ht 0 hcell
  intro x hx
  obtain ⟨e, he⟩ := Q.gap_cover hx
  exact (hall e x he).1

theorem SignedPeriodicPointPartition.eq_zero_of_nonnegative_zero
    (Q : SignedPeriodicPointPartition P n) {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ}
    {c : ℝ}
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => c * u x)
      (Q.point e.castSucc) (Q.point e.succ))
    (ht : SignedPeriodicPointTransmission Q u j)
    (hn : ∀ y ∈ Icc l r, 0 ≤ u y) {x : ℝ} (hx : x ∈ Icc l r) (hz : u x = 0) :
    ∀ y ∈ Icc l r, u y = 0 := by
  by_cases hl : x = l
  · subst x
    exact Q.eq_zero_of_nonnegative_seam_zero hj ht hn hz
  by_cases hr : x = r
  · subst x
    exact Q.eq_zero_of_nonnegative_seam_zero hj ht hn (ht.periodic_state.trans hz)
  exact Q.eq_zero_of_nonnegative_interior_zero hj ht hn
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hl), lt_of_le_of_ne hx.2 hr⟩ hz

end TimeTraps.Analysis
