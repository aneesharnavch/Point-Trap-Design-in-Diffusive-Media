module

public import TimeTraps.Analysis.IntervalPointSpectrum

@[expose] public section

/-! Exact operator/weak-eigenfunction correspondence for every H1 state,
not only for the constructed basis. The physical equation retains all
signed energy tests. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι]

theorem UnitPointProblem.operator_eigen_iff_hilbert (P : UnitPointProblem ι)
    (u : UnitIntervalSobolev) (ev : ℝ) :
    (u.state, ev • u.state) ∈ P.operator.graph ↔
      ∀ v : UnitIntervalSobolev, P.form u v = ev * inner ℝ u.state v.state := by
  rw [P.operator_graph_iff_hilbert]
  constructor
  · rintro ⟨w, hw, he⟩
    have hwu : w = u := ext_state hw
    subst w
    simpa only [real_inner_smul_left] using he
  · intro he
    exact ⟨u, rfl, by simpa only [real_inner_smul_left] using he⟩

theorem UnitPointProblem.hilbert_eigen_iff_physical (P : UnitPointProblem ι)
    (u : UnitIntervalSobolev) (ev : ℝ) :
    (∀ v : UnitIntervalSobolev, P.form u v = ev * inner ℝ u.state v.state) ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
        unitPointForm P.diffusivity P.strength P.site (u.representative zero_lt_one) v =
          ev * ∫ x in (0 : ℝ)..1, u.representative zero_lt_one x * v x := by
  constructor
  · intro he v hv
    have h := he (ofEnergy hv zero_lt_one)
    change unitSobolevForm P.diffusivity P.strength P.site P.site_mem
      u (ofEnergy hv zero_lt_one) = _ at h
    rw [unitSobolevForm_apply, state_inner _ _ zero_lt_one] at h
    rw [unitPointForm_congr P.diffusivity P.strength P.site P.site_mem (fun _ _ => rfl)
      (representative_ofEnergy hv zero_lt_one)] at h
    calc
      _ = ev * ∫ x in (0 : ℝ)..1, u.representative zero_lt_one x *
          (ofEnergy hv zero_lt_one).representative zero_lt_one x := h
      _ = _ := by
        congr 1
        apply intervalIntegral.integral_congr_Ioo_of_le zero_le_one
        intro x hx
        change u.representative zero_lt_one x *
          (ofEnergy hv zero_lt_one).representative zero_lt_one x =
          u.representative zero_lt_one x * v x
        rw [representative_ofEnergy hv zero_lt_one (Ioo_subset_Icc_self hx)]
  · intro he v
    change unitSobolevForm P.diffusivity P.strength P.site P.site_mem u v = _
    rw [unitSobolevForm_apply, state_inner _ _ zero_lt_one]
    exact he (v.representative zero_lt_one) (v.representative_spec zero_lt_one).1

theorem UnitPointProblem.operator_eigen_iff_physical (P : UnitPointProblem ι)
    (u : UnitIntervalSobolev) (ev : ℝ) :
    (u.state, ev • u.state) ∈ P.operator.graph ↔
      ∀ v : ℝ → ℝ, IntervalEnergy v 0 1 →
        unitPointForm P.diffusivity P.strength P.site (u.representative zero_lt_one) v =
          ev * ∫ x in (0 : ℝ)..1, u.representative zero_lt_one x * v x :=
  (P.operator_eigen_iff_hilbert u ev).trans (P.hilbert_eigen_iff_physical u ev)

end TimeTraps.Analysis
