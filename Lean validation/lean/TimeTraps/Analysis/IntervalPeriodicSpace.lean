module

public import TimeTraps.Analysis.IntervalSobolevSpaceEvaluation
public import TimeTraps.Analysis.IntervalSobolevCompactL2
public import TimeTraps.Analysis.IntervalSobolevSpacePairing

@[expose] public section

/-! The full periodic H1 space on a nondegenerate interval is the kernel
of the difference of its two continuous endpoint traces. It is an actual
closed Hilbert subspace of the independent AC/L2 Sobolev space. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

structure IntervalPeriodicBoundary (l r : ℝ) where
  interval_pos : l < r

variable {l r : ℝ}

noncomputable def IntervalPeriodicBoundary.subspace (B : IntervalPeriodicBoundary l r) :
    Submodule ℝ (IntervalSobolevSpace l r) :=
  (evalL B.interval_pos r ⟨B.interval_pos.le, le_rfl⟩ -
    evalL B.interval_pos l ⟨le_rfl, B.interval_pos.le⟩).ker

theorem IntervalPeriodicBoundary.subspace_mem_iff (B : IntervalPeriodicBoundary l r)
    (u : IntervalSobolevSpace l r) :
    u ∈ B.subspace ↔ u.representative B.interval_pos r = u.representative B.interval_pos l := by
  change u.representative B.interval_pos r - u.representative B.interval_pos l = 0 ↔ _
  exact sub_eq_zero

theorem IntervalPeriodicBoundary.subspace_isClosed (B : IntervalPeriodicBoundary l r) :
    IsClosed (B.subspace : Set (IntervalSobolevSpace l r)) :=
  (evalL B.interval_pos r ⟨B.interval_pos.le, le_rfl⟩ -
    evalL B.interval_pos l ⟨le_rfl, B.interval_pos.le⟩).isClosed_ker

abbrev IntervalPeriodicSpace (B : IntervalPeriodicBoundary l r) := ↥B.subspace

instance intervalPeriodicSpace_complete (B : IntervalPeriodicBoundary l r) :
    CompleteSpace (IntervalPeriodicSpace B) := B.subspace_isClosed.completeSpace_coe

theorem IntervalPeriodicBoundary.representative_periodic (B : IntervalPeriodicBoundary l r)
    (u : IntervalPeriodicSpace B) :
    u.val.representative B.interval_pos r = u.val.representative B.interval_pos l :=
  (B.subspace_mem_iff u.val).mp u.property

noncomputable def IntervalPeriodicBoundary.stateL (B : IntervalPeriodicBoundary l r) :
    IntervalPeriodicSpace B →L[ℝ] IntervalSobolevL2 l r :=
  (IntervalSobolevSpace.stateL l r).comp B.subspace.subtypeL

theorem IntervalPeriodicBoundary.stateL_injective (B : IntervalPeriodicBoundary l r) :
    Function.Injective B.stateL := by
  intro u v huv
  apply Subtype.ext
  exact ext_state huv

theorem IntervalPeriodicBoundary.stateL_compact (B : IntervalPeriodicBoundary l r) :
    IsCompactOperator B.stateL :=
  (stateL_isCompact B.interval_pos).comp_clm B.subspace.subtypeL

noncomputable def IntervalPeriodicBoundary.ofEnergy (B : IntervalPeriodicBoundary l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hperiodic : u r = u l) :
    IntervalPeriodicSpace B :=
  ⟨IntervalSobolevSpace.ofEnergy hu B.interval_pos, (B.subspace_mem_iff _).mpr (by
    rw [representative_ofEnergy hu B.interval_pos ⟨B.interval_pos.le, le_rfl⟩,
      representative_ofEnergy hu B.interval_pos ⟨le_rfl, B.interval_pos.le⟩]
    exact hperiodic)⟩

theorem IntervalPeriodicBoundary.ofEnergy_state_ae (B : IntervalPeriodicBoundary l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hperiodic : u r = u l) :
    B.stateL (B.ofEnergy hu hperiodic) =ᵐ[volume.restrict (Ioo l r)] u :=
  (IntervalSobolevSpace.ofEnergy_spec hu B.interval_pos).1

theorem IntervalPeriodicBoundary.ofEnergy_representative (B : IntervalPeriodicBoundary l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (hperiodic : u r = u l) :
    EqOn ((B.ofEnergy hu hperiodic).val.representative B.interval_pos) u (Icc l r) :=
  representative_ofEnergy hu B.interval_pos

theorem IntervalPeriodicBoundary.ofEnergy_representative_eq (B : IntervalPeriodicBoundary l r)
    (u : IntervalPeriodicSpace B) :
    B.ofEnergy ((u.val.representative_spec B.interval_pos).1)
      (B.representative_periodic u) = u := by
  apply Subtype.ext
  exact IntervalSobolevSpace.ofEnergy_representative u.val B.interval_pos

end TimeTraps.Analysis
