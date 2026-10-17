module

public import TimeTraps.Analysis.SignedIntervalPointPositiveGround

@[expose] public section

/-! A principal weak eigenstate is determined by its left trace. If that
trace vanishes, absolute value would give a nonnegative minimizer with a
zero, contradicting the derived strict positivity. This yields simplicity
on the entire actual H1 weak eigenspace, without sign restrictions. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.principal_hilbert_zero_of_left_trace
    (P : SignedIntervalPointProblem ι l r) (u : IntervalSobolevSpace l r)
    (he : ∀ v : IntervalSobolevSpace l r,
      P.form u v = P.principalValue * inner ℝ u.state v.state)
    (hz : u.representative P.interval_pos l = 0) : u = 0 := by
  by_contra hu
  have hs : u.state ≠ 0 := by
    intro h
    apply hu
    apply ext_state
    exact h
  let U := u.representative P.interval_pos
  have hU : IntervalEnergy U l r := (u.representative_spec P.interval_pos).1
  have hm : 0 < P.squareMass U := by
    rw [P.squareMass_representative]
    exact sq_pos_of_pos (norm_pos_iff.mpr hs)
  have hmin : P.quadraticForm U / P.squareMass U = P.principalValue := by
    apply (div_eq_iff hm.ne').mpr
    rw [P.quadraticForm_representative, P.squareMass_representative, he u,
      real_inner_self_eq_norm_sq]
  have hma : 0 < P.squareMass (fun x => |U x|) := by rwa [P.squareMass_abs]
  have hmina : P.quadraticForm (fun x => |U x|) / P.squareMass (fun x => |U x|) =
      P.principalValue := by rwa [P.quadraticForm_abs hU, P.squareMass_abs]
  have hp := P.nonnegative_minimizer_pos hU.abs hma hmina (fun x _ => abs_nonneg (U x))
    l ⟨le_rfl, P.interval_pos.le⟩
  change 0 < |u.representative P.interval_pos l| at hp
  rw [hz, abs_zero] at hp
  exact (lt_irrefl 0 hp)

theorem SignedIntervalPointProblem.principal_hilbert_scalar
    (P : SignedIntervalPointProblem ι l r) (u v : IntervalSobolevSpace l r)
    (hu₀ : u.representative P.interval_pos l ≠ 0)
    (hu : ∀ w : IntervalSobolevSpace l r,
      P.form u w = P.principalValue * inner ℝ u.state w.state)
    (hv : ∀ w : IntervalSobolevSpace l r,
      P.form v w = P.principalValue * inner ℝ v.state w.state) :
    v = (v.representative P.interval_pos l / u.representative P.interval_pos l) • u := by
  let c := v.representative P.interval_pos l / u.representative P.interval_pos l
  have he : ∀ w : IntervalSobolevSpace l r,
      P.form (v - c • u) w = P.principalValue * inner ℝ (v - c • u).state w.state := by
    intro w
    have hs : (v - c • u).state = v.state - c • u.state := by
      change stateL l r (v - c • u) = stateL l r v - c • stateL l r u
      simp only [map_sub, map_smul]
    rw [hs]
    simp only [map_sub, map_smul, sub_apply, smul_apply, smul_eq_mul,
      inner_sub_left, real_inner_smul_left, hu, hv]
    ring
  have hz : (v - c • u).representative P.interval_pos l = 0 := by
    change evalL P.interval_pos l ⟨le_rfl, P.interval_pos.le⟩ (v - c • u) = 0
    simp only [map_sub, map_smul, smul_eq_mul]
    change v.representative P.interval_pos l - c * u.representative P.interval_pos l = 0
    dsimp only [c]
    rw [div_mul_cancel₀ _ hu₀, sub_self]
  exact sub_eq_zero.mp (P.principal_hilbert_zero_of_left_trace (v - c • u) he hz)

end TimeTraps.Analysis
