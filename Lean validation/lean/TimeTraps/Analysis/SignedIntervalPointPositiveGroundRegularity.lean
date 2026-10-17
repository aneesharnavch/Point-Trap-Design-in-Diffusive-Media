module

public import TimeTraps.Analysis.SignedIntervalPointMinimizerPhysical
public import TimeTraps.Analysis.SignedIntervalPointStrongDomain

@[expose] public section

/-! The actual minimizer equation produces a finite contact partition
whose slope equations have the continuous right-hand side -(lambda/D)u.
This continuity is a consequence of the eigen-equation and H1 membership. -/

namespace TimeTraps.Analysis

open Set MeasureTheory Filter IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

theorem SignedIntervalPointProblem.minimizer_linear_piecewise
    (P : SignedIntervalPointProblem ι l r) {u : ℝ → ℝ}
    (hu : IntervalEnergy u l r) (hm : 0 < P.squareMass u)
    (hmin : P.quadraticForm u / P.squareMass u = P.principalValue) :
    ∃ (n : ℕ) (Q : SignedIntervalPointPartition P n) (j : Fin (n + 1) → ℝ → ℝ),
      (∀ e, IntervalSlopeRegularity u (j e)
        (fun x => (-P.principalValue / P.diffusivity) * u x)
        (Q.point e.castSucc) (Q.point e.succ)) ∧ SignedIntervalPointTransmission Q u j := by
  let v := ofEnergy hu P.interval_pos
  let f : IntervalSobolevL2 l r := P.principalValue • v.state
  have hg : (v.state, f) ∈ P.operator.graph := P.minimizer_operator_graph hu hm hmin
  have hw := (P.operator_graph_iff_physical f hu).mp hg
  obtain ⟨n, ⟨Q⟩⟩ := P.exists_partition
  obtain ⟨j, hj, ht⟩ := Q.weak_piecewise_regularity f hu hw
  have hf : f =ᵐ[volume.restrict (Ioo l r)] (fun x => P.principalValue * u x) := by
    filter_upwards [Lp.coeFn_smul P.principalValue v.state,
      (ofEnergy_spec hu P.interval_pos).1] with x hx hy
    change f x = P.principalValue * v.state x at hx
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
