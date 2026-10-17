module

public import TimeTraps.Spectral.Shooting
public import TimeTraps.Spectral.FirstZero

@[expose] public section

/-!
At a nonnegative shooting profile, a zero can only occur at the final right
endpoint, where its derivative is strictly negative. Interior zeros violate
Fermat's theorem and invertibility; at a trap the two one-sided signs and
the zero reaction jump force both derivatives to vanish.
-/

namespace TimeTraps.Spectral

open Set

variable {n : ℕ}

theorem ShootingData.left_positive_of_nonnegative (S : ShootingData n) {k : ℝ}
    (hu : ∀ e, ∀ x ∈ Icc (0 : ℝ) (S.gap e), 0 ≤ S.value k e x) (e : Fin (n + 1)) :
    0 < S.value k e 0 := by
  refine Fin.cases ?_ (fun i => ?_) e
  · rw [S.left_value]
    exact zero_lt_one
  · have hnonneg := hu i.succ 0 ⟨le_rfl, (S.gap_pos i.succ).le⟩
    by_contra h
    have hz : S.value k i.succ 0 = 0 := le_antisymm (le_of_not_gt h) hnonneg
    have hprev : S.value k i.castSucc (S.gap i.castSucc) = 0 := by
      rw [← S.value_matching, hz]
    have hl := derivative_nonpos_at_right_minimum (S.gap_pos i.castSucc)
      (fun x hx => by rw [hprev]; exact hu i.castSucc x hx)
      (S.value_hasDerivAt k i.castSucc (S.gap i.castSucc))
    have hr := derivative_nonneg_at_left_minimum (S.gap_pos i.succ)
      (fun x hx => by rw [hz]; exact hu i.succ x hx)
      (S.value_hasDerivAt k i.succ 0)
    have hj := S.slope_jump k i
    rw [hprev, mul_zero, add_zero] at hj
    have hd : S.slope k i.succ 0 = 0 := by linarith
    exact S.value_slope_ne_zero k i.succ 0 (Prod.ext hz hd)

theorem ShootingData.right_positive_before_last (S : ShootingData n) {k : ℝ}
    (hu : ∀ e, ∀ x ∈ Icc (0 : ℝ) (S.gap e), 0 ≤ S.value k e x) (i : Fin n) :
    0 < S.value k i.castSucc (S.gap i.castSucc) := by
  rw [← S.value_matching]
  exact S.left_positive_of_nonnegative hu i.succ

theorem ShootingData.interior_positive_of_nonnegative (S : ShootingData n) {k : ℝ}
    (hu : ∀ e, ∀ x ∈ Icc (0 : ℝ) (S.gap e), 0 ≤ S.value k e x)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) (S.gap e)) : 0 < S.value k e x := by
  by_contra h
  have hz : S.value k e x = 0 := le_antisymm (le_of_not_gt h) (hu e x (Ioo_subset_Icc_self hx))
  have hd := derivative_zero_at_interior_minimum hx
    (fun y hy => by rw [hz]; exact hu e y hy) (S.value_hasDerivAt k e x)
  exact S.value_slope_ne_zero k e x (Prod.ext hz hd)

theorem ShootingData.zero_only_at_final_endpoint (S : ShootingData n) {k : ℝ}
    (hu : ∀ e, ∀ x ∈ Icc (0 : ℝ) (S.gap e), 0 ≤ S.value k e x)
    (e : Fin (n + 1)) {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (S.gap e))
    (hz : S.value k e x = 0) : e = Fin.last n ∧ x = S.gap e := by
  have hxp : 0 < x := lt_of_le_of_ne hx.1 (by
    intro he
    exact (ne_of_gt (S.left_positive_of_nonnegative hu e)) ((congrArg (S.value k e) he).trans hz))
  have hxe : x = S.gap e := by
    by_contra he
    have hp := S.interior_positive_of_nonnegative hu e ⟨hxp, lt_of_le_of_ne hx.2 he⟩
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  refine ⟨?_, hxe⟩
  rw [hxe] at hz
  revert hz
  refine Fin.lastCases (fun _ => rfl) (fun i hi => ?_) e
  have hp := S.right_positive_before_last hu i
  rw [hi] at hp
  exact (lt_irrefl 0 hp).elim

theorem ShootingData.residual_neg_at_zero (S : ShootingData n) {k : ℝ}
    (hu : ∀ e, ∀ x ∈ Icc (0 : ℝ) (S.gap e), 0 ≤ S.value k e x)
    (hz : S.value k (Fin.last n) (S.gap (Fin.last n)) = 0) : S.residual k < 0 := by
  have hd := derivative_nonpos_at_right_minimum (S.gap_pos (Fin.last n))
    (fun x hx => by rw [hz]; exact hu (Fin.last n) x hx)
    (S.value_hasDerivAt k (Fin.last n) (S.gap (Fin.last n)))
  apply lt_of_le_of_ne hd
  intro he
  exact S.value_slope_ne_zero k (Fin.last n) (S.gap (Fin.last n)) (Prod.ext hz he)

end TimeTraps.Spectral
