module

public import TimeTraps.Analysis.IntervalSobolevSpaceEvaluation
public import TimeTraps.Analysis.IntervalSobolevCompactL2

@[expose] public section

/-! Independent full H1 spaces with any selected endpoint traces fixed to
zero, including the empty selection for unrestricted endpoint values. The zero-trace space is an actual closed Hilbert subspace; it is not
defined by an eigenfunction or a differential-equation ansatz. -/

namespace TimeTraps.Analysis

open Set IntervalSobolevSpace

structure IntervalSeparatedBoundary (l r : ℝ) where
  interval_pos : l < r
  zero_sites : Finset ℝ
  boundary_only : ∀ z ∈ zero_sites, z = l ∨ z = r

variable {l r : ℝ}

theorem IntervalSeparatedBoundary.site_mem (B : IntervalSeparatedBoundary l r)
    {z : ℝ} (hz : z ∈ B.zero_sites) : z ∈ Icc l r := by
  rcases B.boundary_only z hz with rfl | rfl
  · exact ⟨le_rfl, B.interval_pos.le⟩
  · exact ⟨B.interval_pos.le, le_rfl⟩

noncomputable def IntervalSeparatedBoundary.subspace (B : IntervalSeparatedBoundary l r) :
    Submodule ℝ (IntervalSobolevSpace l r) :=
  ⨅ z : B.zero_sites, (evalL B.interval_pos (z : ℝ) (B.site_mem z.property)).ker

theorem IntervalSeparatedBoundary.subspace_mem_iff (B : IntervalSeparatedBoundary l r)
    (u : IntervalSobolevSpace l r) :
    u ∈ B.subspace ↔ ∀ z ∈ B.zero_sites, u.representative B.interval_pos z = 0 := by
  simp only [IntervalSeparatedBoundary.subspace, Submodule.mem_iInf, LinearMap.mem_ker,
    ContinuousLinearMap.coe_coe, evalL_apply, Subtype.forall]

theorem IntervalSeparatedBoundary.subspace_isClosed (B : IntervalSeparatedBoundary l r) :
    IsClosed (B.subspace : Set (IntervalSobolevSpace l r)) := by
  unfold IntervalSeparatedBoundary.subspace
  rw [Submodule.coe_iInf]
  exact isClosed_iInter fun z => (evalL B.interval_pos (z : ℝ) (B.site_mem z.property)).isClosed_ker

abbrev IntervalSeparatedSpace (B : IntervalSeparatedBoundary l r) := ↥B.subspace

instance intervalSeparatedSpace_complete (B : IntervalSeparatedBoundary l r) :
    CompleteSpace (IntervalSeparatedSpace B) := B.subspace_isClosed.completeSpace_coe

noncomputable instance intervalSeparatedSpace_normedSpace (B : IntervalSeparatedBoundary l r) :
    NormedSpace ℝ (IntervalSeparatedSpace B) := Submodule.normedSpace B.subspace

noncomputable def IntervalSeparatedBoundary.stateL (B : IntervalSeparatedBoundary l r) :
    IntervalSeparatedSpace B →L[ℝ] IntervalSobolevL2 l r :=
  (IntervalSobolevSpace.stateL l r).comp B.subspace.subtypeL

theorem IntervalSeparatedBoundary.stateL_injective (B : IntervalSeparatedBoundary l r) :
    Function.Injective B.stateL := by
  intro u v huv
  apply Subtype.ext
  exact ext_state huv

theorem IntervalSeparatedBoundary.stateL_compact (B : IntervalSeparatedBoundary l r) :
    IsCompactOperator B.stateL :=
  (stateL_isCompact B.interval_pos).comp_clm B.subspace.subtypeL

end TimeTraps.Analysis
