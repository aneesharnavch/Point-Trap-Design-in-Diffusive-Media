module

public import TimeTraps.Analysis.RegularSturmPhysical

@[expose] public section

/-! The original operator eigenvalue equation is exactly the full
physical weak Sturm equation with speed-weighted mass. Every selected-endpoint
H1 function is a test; the equivalence is not restricted to basis states. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.stateL_inner (P : RegularSturmProblem ι l r)
    (u v : IntervalSeparatedSpace P.boundary) :
    inner ℝ (P.stateL u) (P.stateL v) = ∫ x in l..r,
      P.speed x * u.val.representative P.boundary.interval_pos x *
        v.val.representative P.boundary.interval_pos x :=
  P.boundary.weightedStateL_inner P.speed P.speed_continuous
    (fun x hx => (P.speed_pos x hx).le) u v

theorem RegularSturmProblem.operator_eigen_iff_hilbert (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) (ev : ℝ) :
    (P.stateL u, ev • P.stateL u) ∈ P.operator.graph ↔
      ∀ v : IntervalSeparatedSpace P.boundary, P.form u v = ev * inner ℝ (P.stateL u) (P.stateL v) := by
  rw [P.operator_graph_iff_state]
  simp only [real_inner_smul_left]

theorem RegularSturmProblem.hilbert_eigen_iff_physical (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) (ev : ℝ) :
    (∀ v : IntervalSeparatedSpace P.boundary, P.form u v = ev * inner ℝ (P.stateL u) (P.stateL v)) ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r → (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r
        (u.val.representative P.boundary.interval_pos) v =
          ev * ∫ x in l..r, P.speed x * u.val.representative P.boundary.interval_pos x * v x) := by
  constructor
  · intro h v hv hvz
    have he := h (P.boundary.ofEnergy hv hvz)
    rw [P.form_apply, P.stateL_inner] at he
    rw [regularSturmPhysicalForm_congr _ _ _ _ P.boundary.interval_pos.le P.site_mem
      (fun _ _ => rfl) (P.boundary.ofEnergy_representative hv hvz)] at he
    calc
      _ = ev * ∫ x in l..r, P.speed x * u.val.representative P.boundary.interval_pos x *
          (P.boundary.ofEnergy hv hvz).val.representative P.boundary.interval_pos x := he
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
        intro x hx
        change P.speed x * u.val.representative P.boundary.interval_pos x *
          (P.boundary.ofEnergy hv hvz).val.representative P.boundary.interval_pos x = _
        rw [P.boundary.ofEnergy_representative hv hvz (Ioo_subset_Icc_self hx)]
  · intro h v
    rw [P.form_apply, P.stateL_inner]
    exact h (v.val.representative P.boundary.interval_pos)
      (v.val.representative_spec P.boundary.interval_pos).1
      (fun _ hx => P.boundary.representative_zero v hx)

theorem RegularSturmProblem.operator_eigen_iff_physical (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) (ev : ℝ) :
    (P.stateL u, ev • P.stateL u) ∈ P.operator.graph ↔
    (∀ v : ℝ → ℝ, IntervalEnergy v l r → (∀ x ∈ P.boundary.zero_sites, v x = 0) →
      regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r
        (u.val.representative P.boundary.interval_pos) v =
          ev * ∫ x in l..r, P.speed x * u.val.representative P.boundary.interval_pos x * v x) :=
  (P.operator_eigen_iff_hilbert u ev).trans (P.hilbert_eigen_iff_physical u ev)

end TimeTraps.Analysis
