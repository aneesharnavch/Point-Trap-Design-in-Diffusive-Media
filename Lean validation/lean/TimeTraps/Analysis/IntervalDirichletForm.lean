module

public import TimeTraps.Analysis.IntervalDirichletSpace
public import TimeTraps.Analysis.IntervalPointFormHilbert

@[expose] public section

/-! The actual point form restricted to the full closed zero-trace H1
subspace. No contact is required to be present or strictly positive. -/

namespace TimeTraps.Analysis

open Set IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable instance intervalDirichletSpace_normedSpace (B : IntervalDirichletBoundary l r) :
    NormedSpace ℝ (IntervalDirichletSpace B) := Submodule.normedSpace B.subspace

noncomputable def intervalDirichletPointForm (B : IntervalDirichletBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) :
    IntervalDirichletSpace B →L[ℝ] IntervalDirichletSpace B →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalDirichletSpace B) := Submodule.seminormedAddCommGroup B.subspace
  letI : NormedSpace ℝ (IntervalDirichletSpace B) := Submodule.normedSpace B.subspace
  let i : IntervalDirichletSpace B →L[ℝ] IntervalSobolevSpace l r := B.subspace.subtypeL
  exact (intervalSobolevPointForm B.interval_pos D κ z hz).bilinearComp i i

theorem intervalDirichletPointForm_apply (B : IntervalDirichletBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r)
    (u v : IntervalDirichletSpace B) :
    intervalDirichletPointForm B D κ z hz u v =
      intervalPointForm D κ z l r
        ((u : IntervalSobolevSpace l r).representative B.interval_pos)
        ((v : IntervalSobolevSpace l r).representative B.interval_pos) := by
  change intervalSobolevPointForm B.interval_pos D κ z hz
    (u : IntervalSobolevSpace l r) (v : IntervalSobolevSpace l r) = _
  exact intervalSobolevPointForm_apply B.interval_pos D κ z hz u v

theorem intervalDirichletPointForm_symmetric (B : IntervalDirichletBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r)
    (u v : IntervalDirichletSpace B) :
    intervalDirichletPointForm B D κ z hz u v = intervalDirichletPointForm B D κ z hz v u :=
  intervalSobolevPointForm_symmetric B.interval_pos D κ z hz u v

theorem IntervalDirichletBoundary.representative_zero (B : IntervalDirichletBoundary l r)
    (u : IntervalDirichletSpace B) {x : ℝ} (hx : x ∈ B.zero_sites) :
    (u : IntervalSobolevSpace l r).representative B.interval_pos x = 0 :=
  (B.subspace_mem_iff u).mp u.property x hx

end TimeTraps.Analysis
