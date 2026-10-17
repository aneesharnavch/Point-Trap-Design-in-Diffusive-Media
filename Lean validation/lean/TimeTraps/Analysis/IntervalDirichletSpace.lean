module

public import TimeTraps.Analysis.IntervalSobolevSpaceEvaluation
public import TimeTraps.Analysis.IntervalSobolevCompactL2

@[expose] public section

/-! Independent full H1 spaces with one or both endpoint traces fixed to
zero. The zero-trace space is an actual closed Hilbert subspace; it is not
defined by an eigenfunction or a differential-equation ansatz. -/

namespace TimeTraps.Analysis

open Set IntervalSobolevSpace

structure IntervalDirichletBoundary (l r : ℝ) where
  interval_pos : l < r
  zero_sites : Finset ℝ
  nonempty : zero_sites.Nonempty
  boundary_only : ∀ z ∈ zero_sites, z = l ∨ z = r

variable {l r : ℝ}

theorem IntervalDirichletBoundary.site_mem (B : IntervalDirichletBoundary l r)
    {z : ℝ} (hz : z ∈ B.zero_sites) : z ∈ Icc l r := by
  rcases B.boundary_only z hz with rfl | rfl
  · exact ⟨le_rfl, B.interval_pos.le⟩
  · exact ⟨B.interval_pos.le, le_rfl⟩

noncomputable def IntervalDirichletBoundary.subspace (B : IntervalDirichletBoundary l r) :
    Submodule ℝ (IntervalSobolevSpace l r) :=
  ⨅ z : B.zero_sites, (evalL B.interval_pos (z : ℝ) (B.site_mem z.property)).ker

theorem IntervalDirichletBoundary.subspace_mem_iff (B : IntervalDirichletBoundary l r)
    (u : IntervalSobolevSpace l r) :
    u ∈ B.subspace ↔ ∀ z ∈ B.zero_sites, u.representative B.interval_pos z = 0 := by
  simp only [IntervalDirichletBoundary.subspace, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, evalL_apply, Subtype.forall]

theorem IntervalDirichletBoundary.subspace_isClosed (B : IntervalDirichletBoundary l r) :
    IsClosed (B.subspace : Set (IntervalSobolevSpace l r)) := by
  unfold IntervalDirichletBoundary.subspace
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun z => (evalL B.interval_pos (z : ℝ) (B.site_mem z.property)).isClosed_ker

abbrev IntervalDirichletSpace (B : IntervalDirichletBoundary l r) := ↥B.subspace

instance intervalDirichletSpace_complete (B : IntervalDirichletBoundary l r) :
    CompleteSpace (IntervalDirichletSpace B) := B.subspace_isClosed.completeSpace_coe

noncomputable def IntervalDirichletBoundary.stateL (B : IntervalDirichletBoundary l r) :
    IntervalDirichletSpace B →L[ℝ] IntervalSobolevL2 l r :=
  (IntervalSobolevSpace.stateL l r).comp B.subspace.subtypeL

theorem IntervalDirichletBoundary.stateL_injective (B : IntervalDirichletBoundary l r) :
    Function.Injective B.stateL := by
  intro u v huv
  apply Subtype.ext
  exact ext_state huv

theorem IntervalDirichletBoundary.stateL_compact (B : IntervalDirichletBoundary l r) :
    IsCompactOperator B.stateL :=
  (stateL_isCompact B.interval_pos).comp_clm B.subspace.subtypeL

end TimeTraps.Analysis
