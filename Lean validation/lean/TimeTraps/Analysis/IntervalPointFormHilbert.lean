module

public import TimeTraps.Analysis.IntervalPointFormCoercive
public import TimeTraps.Analysis.IntervalSobolevSpaceEvaluation
public import TimeTraps.Analysis.IntervalSobolevSpacePairing
public import Mathlib.Analysis.Normed.Operator.Mul
public import Mathlib.Analysis.InnerProductSpace.LaxMilgram

@[expose] public section

/-! The physical point-contact form as a bounded coercive form on the
independent full H1 Hilbert space of an arbitrary finite interval. -/

namespace TimeTraps.Analysis

open Set InnerProductSpace IntervalSobolevSpace
open scoped BigOperators

noncomputable section

def intervalSobolevGradientForm (l r : ℝ) :
    IntervalSobolevSpace l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (gradientL l r) (gradientL l r)

def intervalSobolevPointForm {ι : Type*} [Fintype ι] {l r : ℝ}
    (hlr : l < r) (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r) :
    IntervalSobolevSpace l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
  D • intervalSobolevGradientForm l r +
    ∑ i, κ i • (ContinuousLinearMap.mul ℝ ℝ).bilinearComp
      (evalL hlr (z i) (hz i)) (evalL hlr (z i) (hz i))

def intervalSobolevL2Load (l r : ℝ) :
    IntervalSobolevL2 l r →L[ℝ] IntervalSobolevSpace l r →L[ℝ] ℝ :=
  (innerSL ℝ).bilinearComp (ContinuousLinearMap.id ℝ (IntervalSobolevL2 l r)) (stateL l r)

theorem intervalSobolevL2Load_apply {l r : ℝ}
    (f : IntervalSobolevL2 l r) (v : IntervalSobolevSpace l r) :
    intervalSobolevL2Load l r f v = inner ℝ f v.state := rfl

theorem intervalSobolevPointForm_apply {ι : Type*} [Fintype ι] {l r : ℝ}
    (hlr : l < r) (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r)
    (u v : IntervalSobolevSpace l r) :
    intervalSobolevPointForm hlr D κ z hz u v =
      intervalPointForm D κ z l r (u.representative hlr) (v.representative hlr) := by
  simp only [intervalSobolevPointForm, intervalSobolevGradientForm, add_apply, smul_apply,
    sum_apply, ContinuousLinearMap.bilinearComp_apply,
    innerSL_apply_apply, ContinuousLinearMap.mul_apply', evalL_apply, smul_eq_mul]
  change D * inner ℝ u.gradient v.gradient +
    ∑ i, κ i * (u.representative hlr (z i) * v.representative hlr (z i)) = _
  rw [gradient_inner u v hlr]
  simp only [intervalPointForm, mul_assoc]

theorem intervalSobolevPointForm_coercive {ι : Type*} [Fintype ι] {l r D : ℝ}
    (hlr : l < r) (hD : 0 < D) (κ z : ι → ℝ) (hκ : ∀ i, 0 ≤ κ i)
    (hz : ∀ i, z i ∈ Icc l r) (k : ι) (hκk : 0 < κ k) :
    IsCoercive (intervalSobolevPointForm hlr D κ z hz) := by
  refine ⟨min (D / (2 * (r - l) ^ 2 + 1)) (κ k / (2 * (r - l))),
    intervalPointForm_coercivity_constant_pos hD hκk hlr, ?_⟩
  intro u
  have h := (u.representative_spec hlr).1.interval_point_form_coercive hD.le hlr hκ k (hz k)
  rw [← u.norm_sq_eq_h1SizeSq hlr, ← intervalSobolevPointForm_apply hlr D κ z hz u u] at h
  simpa only [pow_two, mul_assoc] using h

theorem intervalSobolevPointForm_symmetric {ι : Type*} [Fintype ι] {l r : ℝ}
    (hlr : l < r) (D : ℝ) (κ z : ι → ℝ) (hz : ∀ i, z i ∈ Icc l r)
    (u v : IntervalSobolevSpace l r) :
    intervalSobolevPointForm hlr D κ z hz u v = intervalSobolevPointForm hlr D κ z hz v u := by
  simp only [intervalSobolevPointForm, intervalSobolevGradientForm,
    add_apply, smul_apply, sum_apply, ContinuousLinearMap.bilinearComp_apply,
    innerSL_apply_apply, ContinuousLinearMap.mul_apply', smul_eq_mul]
  rw [real_inner_comm (gradientL l r u) (gradientL l r v)]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (evalL hlr (z i) (hz i) u)]

end

end TimeTraps.Analysis
