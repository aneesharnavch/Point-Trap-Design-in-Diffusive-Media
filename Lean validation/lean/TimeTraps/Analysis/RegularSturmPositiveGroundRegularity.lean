module

public import TimeTraps.Analysis.RegularSturmSpectrumEquivalence
public import TimeTraps.Analysis.RegularSturmRegularityDomain

@[expose] public section

/-! Every actual regular Sturm weak eigenstate has the continuous first-order
cell system u'=j/p and j'=(q-lambda*w)u. The selected zero traces and all unselected
Robin/Neumann laws are retained in the derived transmission certificate. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem RegularSturmProblem.eigen_linear_piecewise
    (P : RegularSturmProblem ι l r) (u : IntervalSeparatedSpace P.boundary) (ev : ℝ)
    (he : ∀ v : IntervalSeparatedSpace P.boundary,
      P.form u v = ev * inner ℝ (P.stateL u) (P.stateL v)) :
    ∃ (n : ℕ) (Q : RegularSturmPartition P n) (j : Fin (n + 1) → ℝ → ℝ),
      (∀ e, IntervalFluxRegularity (u.val.representative P.boundary.interval_pos) (j e)
        (fun x => (P.potential x - ev * P.speed x) * u.val.representative P.boundary.interval_pos x) P.conductance
        (Q.point e.castSucc) (Q.point e.succ)) ∧
      RegularSturmTransmission Q (u.val.representative P.boundary.interval_pos) j := by
  let U := u.val.representative P.boundary.interval_pos
  have hU : IntervalEnergy U l r := (u.val.representative_spec P.boundary.interval_pos).1
  have huz : ∀ x ∈ P.boundary.zero_sites, U x = 0 :=
    fun _ hx => P.boundary.representative_zero u hx
  let f : IntervalSobolevL2 l r := ev • P.stateL u
  have hg : (P.stateL u, f) ∈ P.operator.graph :=
    (P.operator_eigen_iff_hilbert u ev).mpr he
  have hg' : (P.stateL (P.boundary.ofEnergy hU huz), f) ∈ P.operator.graph := by
    rw [P.boundary.ofEnergy_representative_eq]
    exact hg
  have hw := (P.operator_graph_iff_physical f hU huz).mp hg'
  obtain ⟨n, ⟨Q⟩⟩ := P.exists_partition
  obtain ⟨j, hj, ht⟩ := Q.weak_piecewise_regularity f hU huz hw
  have hf : f =ᵐ[volume.restrict (Ioo l r)] (fun x => ev * (Real.sqrt (P.speed x) * U x)) := by
    filter_upwards [Lp.coeFn_smul ev (P.stateL u),
      P.stateL_representative_ae u] with x hx hy
    change f x = ev * P.stateL u x at hx
    rw [hx, hy]
  refine ⟨n, Q, j, fun e => ?_, ht⟩
  refine ⟨(hj e).state_energy, (hj e).flux_energy, (hj e).flux_ae, ?_⟩
  have hf' := hf.filter_mono (ae_mono (Measure.restrict_mono_set volume
    (show Ioo (Q.point e.castSucc) (Q.point e.succ) ⊆ Ioo l r from
      Ioo_subset_Ioo (Q.point_mem e.castSucc).1 (Q.point_mem e.succ).2)))
  filter_upwards [(hj e).source_ae, hf',
    ae_restrict_mem (μ := volume) measurableSet_Ioo] with x hx hfx hmem
  rw [hx, hfx]
  have hspeed : 0 ≤ P.speed x := (P.speed_pos x
    (Icc_subset_Icc (Q.point_mem e.castSucc).1 (Q.point_mem e.succ).2
      (Ioo_subset_Icc_self hmem))).le
  calc
    _ = (P.potential x - ev * (Real.sqrt (P.speed x)) ^ 2) * U x := by ring
    _ = _ := by rw [Real.sq_sqrt hspeed]

end TimeTraps.Analysis
