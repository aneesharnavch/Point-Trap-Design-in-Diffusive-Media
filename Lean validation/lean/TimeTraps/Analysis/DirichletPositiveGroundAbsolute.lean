module

public import TimeTraps.Analysis.DirichletPositiveGroundVariational
public import TimeTraps.Analysis.IntervalEnergyAbsolute

@[expose] public section

/-! Absolute value stays in the actual selected-zero-trace H1 space and
preserves the point form and L2 mass. Applied to the first eigenstate, it
gives a normalized nonnegative eigenstate, with its weak equation derived
from the full admissible variational bound. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def IntervalDirichletBoundary.absState (B : IntervalDirichletBoundary l r)
    (u : IntervalDirichletSpace B) : IntervalDirichletSpace B :=
  B.ofEnergy (u.val.representative_spec B.interval_pos).1.abs
    (fun x hx => by rw [B.representative_zero u hx, abs_zero])

theorem IntervalDirichletBoundary.absState_representative (B : IntervalDirichletBoundary l r)
    (u : IntervalDirichletSpace B) :
    EqOn ((B.absState u).val.representative B.interval_pos)
      (fun x => |u.val.representative B.interval_pos x|) (Icc l r) :=
  B.ofEnergy_representative _ _

theorem IntervalDirichletBoundary.absState_mass (B : IntervalDirichletBoundary l r)
    (u : IntervalDirichletSpace B) : ‖B.stateL (B.absState u)‖ ^ 2 = ‖B.stateL u‖ ^ 2 := by
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

theorem DirichletPointProblem.absState_form (P : DirichletPointProblem ι l r)
    (u : IntervalDirichletSpace P.boundary) :
    P.form (P.boundary.absState u) (P.boundary.absState u) = P.form u u := by
  change intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem _ _ =
    intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem _ _
  rw [intervalDirichletPointForm_apply, intervalDirichletPointForm_apply]
  rw [intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le P.site_mem
    (P.boundary.absState_representative u) (P.boundary.absState_representative u)]
  exact (u.val.representative_spec P.boundary.interval_pos).1.abs_point_form
    P.diffusivity P.strength P.site

theorem DirichletPointProblem.nonnegative_first_eigenstate (P : DirichletPointProblem ι l r) :
    ∃ u : IntervalDirichletSpace P.boundary,
      (∀ x ∈ Icc l r, 0 ≤ u.val.representative P.boundary.interval_pos x) ∧
      ‖P.boundary.stateL u‖ ^ 2 = 1 ∧
      ∀ v : IntervalDirichletSpace P.boundary,
        P.form u v = P.firstEigenvalue * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v) := by
  let v := P.eigenstate (P.spectralEnumeration 0)
  let u := P.boundary.absState v
  have he : P.form u u = P.firstEigenvalue * ‖P.boundary.stateL u‖ ^ 2 := by
    change P.form (P.boundary.absState v) (P.boundary.absState v) = _
    rw [P.absState_form, P.boundary.absState_mass]
    simpa only [v, firstEigenvalue, real_inner_self_eq_norm_sq] using
      P.eigenstate_weak (P.spectralEnumeration 0) v
  refine ⟨u, ?_, ?_, P.first_minimizer_hilbert u he⟩
  · intro x hx
    rw [P.boundary.absState_representative v hx]
    exact abs_nonneg _
  · change ‖P.boundary.stateL (P.boundary.absState v)‖ ^ 2 = 1
    rw [P.boundary.absState_mass, P.eigenstate_state,
      P.eigenbasis.orthonormal.norm_eq_one]
    norm_num

end TimeTraps.Analysis
