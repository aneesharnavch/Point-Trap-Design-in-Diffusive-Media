module

public import TimeTraps.Analysis.SignedPeriodicPointSpectrumEquivalence
public import TimeTraps.Analysis.SignedPeriodicPointRegularityDomain

@[expose] public section

/-! Every arbitrary-real-contact periodic weak eigenstate satisfies
the continuous linear cell equation, with its actual signed seam law. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedPeriodicPointProblem.eigen_linear_piecewise
    (P : SignedPeriodicPointProblem ι l r) (u : IntervalPeriodicSpace P.boundary) (ev : ℝ)
    (he : ∀ v : IntervalPeriodicSpace P.boundary,
      P.form u v = ev * inner ℝ (P.boundary.stateL u) (P.boundary.stateL v)) :
    ∃ (n : ℕ) (Q : SignedPeriodicPointPartition P n) (j : Fin (n + 1) → ℝ → ℝ),
      (∀ e, IntervalSlopeRegularity (u.val.representative P.boundary.interval_pos) (j e)
        (fun x => (-ev / P.diffusivity) * u.val.representative P.boundary.interval_pos x)
        (Q.point e.castSucc) (Q.point e.succ)) ∧
      SignedPeriodicPointTransmission Q (u.val.representative P.boundary.interval_pos) j := by
  let U := u.val.representative P.boundary.interval_pos
  have hU : IntervalEnergy U l r := (u.val.representative_spec P.boundary.interval_pos).1
  have huz : U l = U r :=
    (P.boundary.representative_periodic u).symm
  let f : IntervalSobolevL2 l r := ev • P.boundary.stateL u
  have hg : (P.boundary.stateL u, f) ∈ P.operator.graph :=
    (P.operator_eigen_iff_hilbert u ev).mpr he
  have hg' : (P.boundary.stateL (P.boundary.ofEnergy hU huz.symm), f) ∈ P.operator.graph := by
    rw [P.boundary.ofEnergy_representative_eq]
    exact hg
  have hw := (P.operator_graph_iff_physical f hU huz).mp hg'
  obtain ⟨n, ⟨Q⟩⟩ := P.exists_partition
  obtain ⟨j, hj, ht⟩ := Q.weak_piecewise_regularity f hU huz hw
  have hf : f =ᵐ[volume.restrict (Ioo l r)] (fun x => ev * U x) := by
    filter_upwards [Lp.coeFn_smul ev (P.boundary.stateL u),
      (u.val.representative_spec P.boundary.interval_pos).2.1] with x hx hy
    change f x = ev * u.val.state x at hx
    rw [hx, hy]
  refine ⟨n, Q, j, fun e => ?_, ht⟩
  refine ⟨(hj e).state_energy, (hj e).slope_energy, (hj e).slope_ae, ?_⟩
  have hf' := hf.filter_mono (ae_mono (Measure.restrict_mono_set volume
    (show Ioo (Q.point e.castSucc) (Q.point e.succ) ⊆ Ioo l r from
      Ioo_subset_Ioo (Q.point_mem e.castSucc).1 (Q.point_mem e.succ).2)))
  filter_upwards [(hj e).second_ae, hf'] with x hx hfx
  rw [hx, hfx]
  ring

end TimeTraps.Analysis
