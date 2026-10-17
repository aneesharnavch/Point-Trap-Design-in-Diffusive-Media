module

public import TimeTraps.Analysis.IntervalPeriodicSpace
public import TimeTraps.Analysis.IntervalPointFormHilbert

@[expose] public section

/-! The physical point form restricted to the full periodic H1 space.
The positive-contact coercivity estimate on the ambient Sobolev space
restricts to this closed subspace without a zero-endpoint condition. -/

namespace TimeTraps.Analysis

open Set IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable instance intervalPeriodicSpace_normedSpace (B : IntervalPeriodicBoundary l r) :
    NormedSpace ℝ (IntervalPeriodicSpace B) := Submodule.normedSpace B.subspace

noncomputable def intervalPeriodicPointForm (B : IntervalPeriodicBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) :
    IntervalPeriodicSpace B →L[ℝ] IntervalPeriodicSpace B →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalPeriodicSpace B) := Submodule.seminormedAddCommGroup B.subspace
  letI : NormedSpace ℝ (IntervalPeriodicSpace B) := Submodule.normedSpace B.subspace
  let i : IntervalPeriodicSpace B →L[ℝ] IntervalSobolevSpace l r := B.subspace.subtypeL
  exact (intervalSobolevPointForm B.interval_pos D κ z hz).bilinearComp i i

theorem intervalPeriodicPointForm_apply (B : IntervalPeriodicBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r)
    (u v : IntervalPeriodicSpace B) :
    intervalPeriodicPointForm B D κ z hz u v =
      intervalPointForm D κ z l r (u.val.representative B.interval_pos)
        (v.val.representative B.interval_pos) :=
  intervalSobolevPointForm_apply B.interval_pos D κ z hz u v

theorem intervalPeriodicPointForm_symmetric (B : IntervalPeriodicBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r)
    (u v : IntervalPeriodicSpace B) :
    intervalPeriodicPointForm B D κ z hz u v = intervalPeriodicPointForm B D κ z hz v u :=
  intervalSobolevPointForm_symmetric B.interval_pos D κ z hz u v

theorem intervalPeriodicPointForm_coercive {D : ℝ} (B : IntervalPeriodicBoundary l r)
    (hD : 0 < D) (κ z : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hz : ∀ i, z i ∈ Icc l r) (k : ι) (hk : 0 < κ k) :
    @IsCoercive (IntervalPeriodicSpace B) (Submodule.seminormedAddCommGroup B.subspace)
      (Submodule.normedSpace B.subspace) (intervalPeriodicPointForm B D κ z hz) := by
  obtain ⟨c, hc, hb⟩ := intervalSobolevPointForm_coercive B.interval_pos hD κ z hκ hz k hk
  refine ⟨c, hc, ?_⟩
  intro u
  exact hb (u : IntervalSobolevSpace l r)

end TimeTraps.Analysis
