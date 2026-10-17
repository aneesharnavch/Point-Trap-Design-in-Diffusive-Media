module

public import TimeTraps.Analysis.IntervalSlopeUniqueness
public import TimeTraps.Analysis.SignedDirichletPointRegularityTransmission

@[expose] public section

/-! A zero solution on one contact-free cell propagates through every
contact, without imposing slope constraints at the absorbing endpoints. At a zero state value the signed jump vanishes, so zero
Cauchy data transfer to the neighboring cell in either direction. -/

namespace TimeTraps.Analysis

open Set MeasureTheory

variable {ι : Type*} [Fintype ι] {l r : ℝ}
variable {P : SignedDirichletPointProblem ι l r} {n : ℕ}

theorem SignedDirichletPointPartition.gap_cover (Q : SignedDirichletPointPartition P n)
    {x : ℝ} (hx : x ∈ Icc l r) :
    ∃ e : Fin (n + 1), x ∈ Icc (Q.point e.castSucc) (Q.point e.succ) := by
  have hc : ∀ e : Fin (n + 1), ∀ y ∈ Icc (Q.point 0) (Q.point e.succ),
      ∃ d : Fin (n + 1), y ∈ Icc (Q.point d.castSucc) (Q.point d.succ) := by
    intro e
    induction e using Fin.induction with
    | zero =>
      intro y hy
      exact ⟨0, hy⟩
    | succ i ih =>
      intro y hy
      by_cases hb : y ≤ Q.point i.castSucc.succ
      · exact ih y ⟨hy.1, hb⟩
      · exact ⟨i.succ, ⟨(lt_of_not_ge hb).le, hy.2⟩⟩
  apply hc (Fin.last n) x
  change x ∈ Icc (Q.point 0) (Q.point (Fin.last (n + 1)))
  simpa only [Q.left_eq, Q.right_eq] using hx

theorem SignedDirichletPointPartition.all_cells_zero_of_cell_zero
    (Q : SignedDirichletPointPartition P n) {u : ℝ → ℝ} {j : Fin (n + 1) → ℝ → ℝ}
    {c : ℝ}
    (hj : ∀ e, IntervalSlopeRegularity u (j e) (fun x => c * u x)
      (Q.point e.castSucc) (Q.point e.succ))
    (ht : SignedDirichletPointTransmission Q u j)
    (e₀ : Fin (n + 1))
    (hzero : ∀ x ∈ Icc (Q.point e₀.castSucc) (Q.point e₀.succ), u x = 0 ∧ j e₀ x = 0) :
    ∀ e, ∀ x ∈ Icc (Q.point e.castSucc) (Q.point e.succ), u x = 0 ∧ j e x = 0 := by
  let C : Fin (n + 1) → Prop := fun e =>
    ∀ x ∈ Icc (Q.point e.castSucc) (Q.point e.succ), u x = 0 ∧ j e x = 0
  have ha (i : Fin n) : C i.castSucc ↔ C i.succ := by
    constructor
    · intro hi
      have hz := hi (Q.point i.castSucc.succ)
        ⟨(Q.strictMono Fin.castSucc_lt_succ).le, le_rfl⟩
      have hjump := ht.interior_jump i
      rw [hz.1, mul_zero, hz.2, sub_zero] at hjump
      have hzj : j i.succ (Q.point i.castSucc.succ) = 0 :=
        (mul_eq_zero.mp hjump).resolve_left P.diffusivity_pos.ne'
      apply (hj i.succ).eq_zero_of_linear_cauchy (Q.strictMono Fin.castSucc_lt_succ)
        (t₀ := Q.point i.castSucc.succ) _ hz.1 hzj
      simpa only [Fin.succ_castSucc] using
        (show Q.point i.succ.castSucc ∈ Icc (Q.point i.succ.castSucc) (Q.point i.succ.succ) from
          ⟨le_rfl, (Q.strictMono Fin.castSucc_lt_succ).le⟩)
    · intro hi
      have hz := hi (Q.point i.castSucc.succ) (by
        simpa only [Fin.succ_castSucc] using
          (show Q.point i.succ.castSucc ∈ Icc (Q.point i.succ.castSucc) (Q.point i.succ.succ) from
            ⟨le_rfl, (Q.strictMono Fin.castSucc_lt_succ).le⟩))
      have hjump := ht.interior_jump i
      rw [hz.1, mul_zero, hz.2, zero_sub] at hjump
      have hzj : j i.castSucc (Q.point i.castSucc.succ) = 0 := by
        have he := (mul_eq_zero.mp hjump).resolve_left P.diffusivity_pos.ne'
        exact neg_eq_zero.mp he
      exact (hj i.castSucc).eq_zero_of_linear_cauchy (Q.strictMono Fin.castSucc_lt_succ)
        ⟨(Q.strictMono Fin.castSucc_lt_succ).le, le_rfl⟩ hz.1 hzj
  have hc (e : Fin (n + 1)) : C e ↔ C 0 := by
    induction e using Fin.induction with
    | zero => rfl
    | succ i ih => exact (ha i).symm.trans ih
  intro e
  exact (hc e).mpr ((hc e₀).mp hzero)

end TimeTraps.Analysis
