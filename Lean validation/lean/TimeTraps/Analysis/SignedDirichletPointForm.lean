module

public import TimeTraps.Analysis.IntervalDirichletFormCoercive
public import TimeTraps.Analysis.IntervalPointFormSemiboundedHilbert

@[expose] public section

/-! The signed point form and its coercive mass shift restricted to the
actual selected-zero H1 subspace. The full-H1 trace estimate supplies the
shift for arbitrary real strengths; the contact family may be empty. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def intervalDirichletShiftedPointForm (B : IntervalDirichletBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ) :
    IntervalDirichletSpace B →L[ℝ] IntervalDirichletSpace B →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalDirichletSpace B) := Submodule.seminormedAddCommGroup B.subspace
  letI : NormedSpace ℝ (IntervalDirichletSpace B) := Submodule.normedSpace B.subspace
  let i : IntervalDirichletSpace B →L[ℝ] IntervalSobolevSpace l r := B.subspace.subtypeL
  exact (intervalSobolevShiftedPointForm B.interval_pos D κ z hz c).bilinearComp i i

theorem intervalDirichletShiftedPointForm_eq (B : IntervalDirichletBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ)
    (u v : IntervalDirichletSpace B) :
    intervalDirichletShiftedPointForm B D κ z hz c u v =
      intervalDirichletPointForm B D κ z hz u v + c * inner ℝ (B.stateL u) (B.stateL v) := rfl

theorem intervalDirichletShiftedPointForm_symmetric (B : IntervalDirichletBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ)
    (u v : IntervalDirichletSpace B) :
    intervalDirichletShiftedPointForm B D κ z hz c u v =
      intervalDirichletShiftedPointForm B D κ z hz c v u :=
  intervalSobolevShiftedPointForm_symmetric B.interval_pos D κ z hz c u.val v.val

theorem intervalDirichletPointForm_semibounded {D : ℝ}
    (B : IntervalDirichletBoundary l r) (hD : 0 < D) (κ z : ι → ℝ)
    (hz : ∀ i, z i ∈ Icc l r) (u : IntervalDirichletSpace B) :
    -(intervalPointNegativeBound D κ l r * ‖B.stateL u‖ ^ 2) ≤
      intervalDirichletPointForm B D κ z hz u u :=
  intervalSobolevPointForm_semibounded B.interval_pos hD κ z hz u.val

theorem intervalDirichletShiftedPointForm_coercive {D : ℝ}
    (B : IntervalDirichletBoundary l r) (hD : 0 < D) (κ z : ι → ℝ)
    (hz : ∀ i, z i ∈ Icc l r) :
    @IsCoercive (IntervalDirichletSpace B) (Submodule.seminormedAddCommGroup B.subspace)
      (Submodule.normedSpace B.subspace) (intervalDirichletShiftedPointForm B D κ z hz
        (intervalPointNegativeBound D κ l r + 1)) := by
  obtain ⟨c, hc, hb⟩ := intervalSobolevShiftedPointForm_coercive B.interval_pos hD κ z hz
  exact ⟨c, hc, fun u => hb u.val⟩

end TimeTraps.Analysis
