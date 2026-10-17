module

public import TimeTraps.Analysis.IntervalPeriodicForm
public import TimeTraps.Analysis.IntervalPointFormSemiboundedHilbert

@[expose] public section

/-! The signed point form and its coercive mass shift restricted to the
actual endpoint-matched periodic H1 subspace. The full-H1 trace estimate supplies the
shift for arbitrary real strengths; the contact family may be empty. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def intervalPeriodicShiftedPointForm (B : IntervalPeriodicBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ) :
    IntervalPeriodicSpace B →L[ℝ] IntervalPeriodicSpace B →L[ℝ] ℝ := by
  letI : SeminormedAddCommGroup (IntervalPeriodicSpace B) := Submodule.seminormedAddCommGroup B.subspace
  letI : NormedSpace ℝ (IntervalPeriodicSpace B) := Submodule.normedSpace B.subspace
  let i : IntervalPeriodicSpace B →L[ℝ] IntervalSobolevSpace l r := B.subspace.subtypeL
  exact (intervalSobolevShiftedPointForm B.interval_pos D κ z hz c).bilinearComp i i

theorem intervalPeriodicShiftedPointForm_eq (B : IntervalPeriodicBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ)
    (u v : IntervalPeriodicSpace B) :
    intervalPeriodicShiftedPointForm B D κ z hz c u v =
      intervalPeriodicPointForm B D κ z hz u v + c * inner ℝ (B.stateL u) (B.stateL v) := rfl

theorem intervalPeriodicShiftedPointForm_symmetric (B : IntervalPeriodicBoundary l r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ)
    (u v : IntervalPeriodicSpace B) :
    intervalPeriodicShiftedPointForm B D κ z hz c u v =
      intervalPeriodicShiftedPointForm B D κ z hz c v u :=
  intervalSobolevShiftedPointForm_symmetric B.interval_pos D κ z hz c u.val v.val

theorem intervalPeriodicPointForm_semibounded {D : ℝ}
    (B : IntervalPeriodicBoundary l r) (hD : 0 < D) (κ z : ι → ℝ)
    (hz : ∀ i, z i ∈ Icc l r) (u : IntervalPeriodicSpace B) :
    -(intervalPointNegativeBound D κ l r * ‖B.stateL u‖ ^ 2) ≤
      intervalPeriodicPointForm B D κ z hz u u :=
  intervalSobolevPointForm_semibounded B.interval_pos hD κ z hz u.val

theorem intervalPeriodicShiftedPointForm_coercive {D : ℝ}
    (B : IntervalPeriodicBoundary l r) (hD : 0 < D) (κ z : ι → ℝ)
    (hz : ∀ i, z i ∈ Icc l r) :
    @IsCoercive (IntervalPeriodicSpace B) (Submodule.seminormedAddCommGroup B.subspace)
      (Submodule.normedSpace B.subspace) (intervalPeriodicShiftedPointForm B D κ z hz
        (intervalPointNegativeBound D κ l r + 1)) := by
  obtain ⟨c, hc, hb⟩ := intervalSobolevShiftedPointForm_coercive B.interval_pos hD κ z hz
  exact ⟨c, hc, fun u => hb u.val⟩

end TimeTraps.Analysis
