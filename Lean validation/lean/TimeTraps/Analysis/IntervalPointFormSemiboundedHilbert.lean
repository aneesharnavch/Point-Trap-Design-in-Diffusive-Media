module

public import TimeTraps.Analysis.IntervalPointFormSemibounded
public import TimeTraps.Analysis.IntervalPointFormHilbert

@[expose] public section

/-! The signed point form and its explicit coercive mass shift on the
actual full H1 Hilbert space. The mass pairing is the original L2 pairing,
and the coercivity norm is the sum of the actual two square integrals. -/

namespace TimeTraps.Analysis

open Set MeasureTheory InnerProductSpace IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def intervalSobolevShiftedPointForm (hlr : l < r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ) :
    IntervalSobolevSpace l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
  let mass : IntervalSobolevSpace l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
    (innerSL ℝ).bilinearComp (stateL l r) (stateL l r)
  intervalSobolevPointForm hlr D κ z hz + c • mass

theorem intervalSobolevShiftedPointForm_apply (hlr : l < r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ)
    (u v : IntervalSobolevSpace l r) :
    intervalSobolevShiftedPointForm hlr D κ z hz c u v =
      intervalPointForm D κ z l r (u.representative hlr) (v.representative hlr) +
        c * ∫ x in l..r, u.representative hlr x * v.representative hlr x := by
  change intervalSobolevPointForm hlr D κ z hz u v + c * inner ℝ u.state v.state = _
  rw [intervalSobolevPointForm_apply, state_inner u v hlr]

theorem intervalSobolevShiftedPointForm_symmetric (hlr : l < r)
    (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (c : ℝ)
    (u v : IntervalSobolevSpace l r) :
    intervalSobolevShiftedPointForm hlr D κ z hz c u v =
      intervalSobolevShiftedPointForm hlr D κ z hz c v u := by
  change intervalSobolevPointForm hlr D κ z hz u v + c * inner ℝ u.state v.state =
    intervalSobolevPointForm hlr D κ z hz v u + c * inner ℝ v.state u.state
  rw [intervalSobolevPointForm_symmetric hlr D κ z hz u v, real_inner_comm u.state v.state]

theorem intervalSobolevPointForm_semibounded {D : ℝ} (hlr : l < r) (hD : 0 < D)
    (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) (u : IntervalSobolevSpace l r) :
    -(intervalPointNegativeBound D κ l r * ‖u.state‖ ^ 2) ≤
      intervalSobolevPointForm hlr D κ z hz u u := by
  have h := (u.representative_spec hlr).1.point_form_semibounded hlr hD κ z hz
  rw [intervalSobolevPointForm_apply, ← real_inner_self_eq_norm_sq, state_inner u u hlr]
  simpa only [pow_two] using h

theorem intervalSobolevShiftedPointForm_coercive {D : ℝ} (hlr : l < r) (hD : 0 < D)
    (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) :
    IsCoercive (intervalSobolevShiftedPointForm hlr D κ z hz
      (intervalPointNegativeBound D κ l r + 1)) := by
  refine ⟨min (D / 2) 1, lt_min (by positivity) zero_lt_one, ?_⟩
  intro u
  have h := (u.representative_spec hlr).1.point_form_shift_coercive hlr hD κ z hz
  rw [← u.norm_sq_eq_h1SizeSq hlr] at h
  simpa only [intervalSobolevShiftedPointForm_apply, pow_two, mul_assoc] using h

end TimeTraps.Analysis
