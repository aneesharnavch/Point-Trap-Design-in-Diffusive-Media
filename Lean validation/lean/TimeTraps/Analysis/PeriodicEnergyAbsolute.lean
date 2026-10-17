module

public import TimeTraps.Analysis.IntervalPeriodicSpace
public import TimeTraps.Analysis.IntervalEnergyAbsolute

@[expose] public section

/-! Absolute value preserves the actual periodic H1 space, matching
endpoint values and the original length L2 mass. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {l r : ℝ}

noncomputable def IntervalPeriodicBoundary.absState (B : IntervalPeriodicBoundary l r)
    (u : IntervalPeriodicSpace B) : IntervalPeriodicSpace B :=
  B.ofEnergy (u.val.representative_spec B.interval_pos).1.abs
    (congrArg abs (B.representative_periodic u))

theorem IntervalPeriodicBoundary.absState_representative (B : IntervalPeriodicBoundary l r)
    (u : IntervalPeriodicSpace B) :
    EqOn ((B.absState u).val.representative B.interval_pos)
      (fun x => |u.val.representative B.interval_pos x|) (Icc l r) :=
  B.ofEnergy_representative _ _

theorem IntervalPeriodicBoundary.absState_mass (B : IntervalPeriodicBoundary l r)
    (u : IntervalPeriodicSpace B) : ‖B.stateL (B.absState u)‖ ^ 2 = ‖B.stateL u‖ ^ 2 := by
  change ‖(B.absState u).val.state‖ ^ 2 = ‖u.val.state‖ ^ 2
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    state_inner _ _ B.interval_pos, state_inner _ _ B.interval_pos]
  apply intervalIntegral.integral_congr_Ioo_of_le B.interval_pos.le
  intro x hx
  change (B.absState u).val.representative B.interval_pos x *
      (B.absState u).val.representative B.interval_pos x =
    u.val.representative B.interval_pos x * u.val.representative B.interval_pos x
  rw [B.absState_representative u (Ioo_subset_Icc_self hx)]
  exact abs_mul_abs_self _

end TimeTraps.Analysis
