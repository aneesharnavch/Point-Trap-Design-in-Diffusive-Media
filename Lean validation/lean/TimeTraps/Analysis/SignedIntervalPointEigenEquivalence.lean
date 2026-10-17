module

public import TimeTraps.Analysis.SignedIntervalPointPhysical

@[expose] public section

/-! Exact unshifted eigen-equation correspondence for every actual H1
state of the signed interval problem. All signed physical H1 tests and
every finite real contact are retained. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.operator_eigen_iff_hilbert (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) (ev : ℝ) :
    (u.state, ev • u.state) ∈ P.operator.graph ↔
      ∀ v : IntervalSobolevSpace l r, P.form u v = ev * inner ℝ u.state v.state := by
  rw [P.operator_graph_iff_state]
  simp only [real_inner_smul_left]

theorem SignedIntervalPointProblem.hilbert_eigen_iff_physical (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) (ev : ℝ) :
    (∀ v : IntervalSobolevSpace l r, P.form u v = ev * inner ℝ u.state v.state) ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r (u.representative P.interval_pos) v =
          ev * ∫ x in l..r, u.representative P.interval_pos x * v x := by
  constructor
  · intro he v hv
    have h := he (ofEnergy hv P.interval_pos)
    change intervalSobolevPointForm P.interval_pos P.diffusivity P.strength P.site P.site_mem
      u (ofEnergy hv P.interval_pos) = _ at h
    rw [intervalSobolevPointForm_apply, state_inner _ _ P.interval_pos] at h
    rw [intervalPointForm_congr P.diffusivity P.strength P.site P.interval_pos.le P.site_mem
      (fun _ _ => rfl) (representative_ofEnergy hv P.interval_pos)] at h
    calc
      _ = ev * ∫ x in l..r, u.representative P.interval_pos x *
          (ofEnergy hv P.interval_pos).representative P.interval_pos x := h
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_Ioo_of_le P.interval_pos.le
        intro x hx
        change u.representative P.interval_pos x *
          (ofEnergy hv P.interval_pos).representative P.interval_pos x =
          u.representative P.interval_pos x * v x
        rw [representative_ofEnergy hv P.interval_pos (Ioo_subset_Icc_self hx)]
  · intro he v
    change intervalSobolevPointForm P.interval_pos P.diffusivity P.strength P.site P.site_mem u v = _
    rw [intervalSobolevPointForm_apply, state_inner _ _ P.interval_pos]
    exact he (v.representative P.interval_pos) (v.representative_spec P.interval_pos).1

theorem SignedIntervalPointProblem.operator_eigen_iff_physical (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) (ev : ℝ) :
    (u.state, ev • u.state) ∈ P.operator.graph ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v l r →
        intervalPointForm P.diffusivity P.strength P.site l r (u.representative P.interval_pos) v =
          ev * ∫ x in l..r, u.representative P.interval_pos x * v x :=
  (P.operator_eigen_iff_hilbert u ev).trans (P.hilbert_eigen_iff_physical u ev)

end TimeTraps.Analysis
