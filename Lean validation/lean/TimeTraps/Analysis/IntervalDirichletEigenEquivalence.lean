module

public import TimeTraps.Analysis.IntervalDirichletPhysicalOperator

@[expose] public section

/-! Exact operator/weak-eigenfunction correspondence for every H1 state,
not only for the constructed basis. The physical equation retains all
signed zero-trace energy tests. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem DirichletPointProblem.operator_eigen_iff_hilbert (P : DirichletPointProblem ι l r)
    (u : IntervalDirichletSpace P.boundary) (ev : ℝ) :
    ((P.boundary.stateL u), ev • (P.boundary.stateL u)) ∈ P.operator.graph ↔
      ∀ v : IntervalDirichletSpace P.boundary, P.form u v = ev * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v) := by
  rw [P.operator_graph_iff_hilbert]
  constructor
  · rintro ⟨w, hw, he⟩
    have hwu : w = u := P.boundary.stateL_injective hw
    subst w
    simpa only [real_inner_smul_left] using he
  · intro he
    exact ⟨u, rfl, by simpa only [real_inner_smul_left] using he⟩

theorem DirichletPointProblem.hilbert_eigen_iff_physical (P : DirichletPointProblem ι l r)
    (u : IntervalDirichletSpace P.boundary) (ev : ℝ) :
    (∀ v : IntervalDirichletSpace P.boundary, P.form u v = ev * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v)) ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ x ∈ P.boundary.zero_sites, v x = 0) →
        intervalPointForm P.diffusivity P.strength P.site l r (u.val.representative P.boundary.interval_pos) v =
          ev * ∫ x in l..r, u.val.representative P.boundary.interval_pos x * v x := by
  constructor
  · intro he v hv hvz
    have h := he (P.boundary.ofEnergy hv hvz)
    change intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem
      u (P.boundary.ofEnergy hv hvz) = _ at h
    rw [intervalDirichletPointForm_apply] at h
    change _ = ev * inner ℝ u.val.state (P.boundary.ofEnergy hv hvz).val.state at h
    rw [state_inner _ _ P.boundary.interval_pos] at h
    rw [intervalPointForm_congr P.diffusivity P.strength P.site P.boundary.interval_pos.le P.site_mem (fun _ _ => rfl)
      (P.boundary.ofEnergy_representative hv hvz)] at h
    calc
      _ = ev * ∫ x in l..r, u.val.representative P.boundary.interval_pos x *
          (P.boundary.ofEnergy hv hvz).val.representative P.boundary.interval_pos x := h
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
        intro x hx
        change u.val.representative P.boundary.interval_pos x *
          (P.boundary.ofEnergy hv hvz).val.representative P.boundary.interval_pos x =
          u.val.representative P.boundary.interval_pos x * v x
        rw [P.boundary.ofEnergy_representative hv hvz (Ioo_subset_Icc_self hx)]
  · intro he v
    change intervalDirichletPointForm P.boundary P.diffusivity P.strength P.site P.site_mem u v = _
    rw [intervalDirichletPointForm_apply]
    change _ = ev * inner ℝ u.val.state v.val.state
    rw [state_inner _ _ P.boundary.interval_pos]
    exact he (v.val.representative P.boundary.interval_pos) (v.val.representative_spec P.boundary.interval_pos).1 (fun _ hx => P.boundary.representative_zero v hx)

theorem DirichletPointProblem.operator_eigen_iff_physical (P : DirichletPointProblem ι l r)
    (u : IntervalDirichletSpace P.boundary) (ev : ℝ) :
    ((P.boundary.stateL u), ev • (P.boundary.stateL u)) ∈ P.operator.graph ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        (∀ x ∈ P.boundary.zero_sites, v x = 0) →
        intervalPointForm P.diffusivity P.strength P.site l r (u.val.representative P.boundary.interval_pos) v =
          ev * ∫ x in l..r, u.val.representative P.boundary.interval_pos x * v x :=
  (P.operator_eigen_iff_hilbert u ev).trans (P.hilbert_eigen_iff_physical u ev)

end TimeTraps.Analysis
