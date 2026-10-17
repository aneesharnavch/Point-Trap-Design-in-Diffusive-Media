module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.MeanValue
public import Mathlib.Tactic.Linarith

@[expose] public section

/-!
Calculus on a closed real interval with continuity assumed only there.
These lemmas keep endpoint continuity distinct from interior differentiability;
no differentiability of the medium coefficients is imposed.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem integral_primitive_continuousOn {f : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hf : ContinuousOn f (Icc l r)) :
    ContinuousOn (fun x => ∫ t in l..x, f t) (Icc l r) := by
  have hi := hf.intervalIntegrable_of_Icc (μ := volume) hlr
  simpa only [uIcc_of_le hlr] using
    intervalIntegral.continuousOn_primitive_interval' hi (left_mem_uIcc : l ∈ uIcc l r)

theorem integral_primitive_hasDerivAt {f : ℝ → ℝ} {l r x : ℝ}
    (hf : ContinuousOn f (Icc l r)) (hx : x ∈ Ioo l r) :
    HasDerivAt (fun y => ∫ t in l..y, f t) (f x) x := by
  have hsub : Icc l x ⊆ Icc l r := Icc_subset_Icc le_rfl hx.2.le
  have hi := (hf.mono hsub).intervalIntegrable_of_Icc (μ := volume) hx.1.le
  have hfo : ContinuousOn f (Ioo l r) := hf.mono Ioo_subset_Icc_self
  exact intervalIntegral.integral_hasDerivAt_right hi
    (hfo.stronglyMeasurableAtFilter isOpen_Ioo x hx)
    (hfo.continuousAt (isOpen_Ioo.mem_nhds hx))

/-- Recover a function from its interior derivative and one endpoint value. -/
theorem integral_derivative_to_point {u g : ℝ → ℝ} {l r x : ℝ}
    (hu : ContinuousOn u (Icc l r)) (hg : ContinuousOn g (Icc l r))
    (hderiv : ∀ y ∈ Ioo l r, HasDerivAt u (g y) y)
    (hx : x ∈ Icc l r) :
    (∫ y in l..x, g y) = u x - u l := by
  have hsub : Icc l x ⊆ Icc l r := Icc_subset_Icc le_rfl hx.2
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx.1 (hu.mono hsub)
    (fun y hy => hderiv y ⟨hy.1, lt_of_lt_of_le hy.2 hx.2⟩)
    ((hg.mono hsub).intervalIntegrable_of_Icc hx.1)

/-- Strictly positive source gives a strictly increasing integrated source. -/
theorem integral_primitive_strictMonoOn {f : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hf : ContinuousOn f (Icc l r))
    (hpos : ∀ x ∈ Ioo l r, 0 < f x) :
    StrictMonoOn (fun x => ∫ t in l..x, f t) (Icc l r) := by
  apply strictMonoOn_of_deriv_pos (convex_Icc l r) (integral_primitive_continuousOn hlr hf)
  intro x hx
  rw [interior_Icc] at hx
  rw [(integral_primitive_hasDerivAt hf hx).deriv]
  exact hpos x hx

end TimeTraps.Analysis
