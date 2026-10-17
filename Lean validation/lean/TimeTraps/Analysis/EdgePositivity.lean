module

public import TimeTraps.Analysis.EdgeReconstruction

@[expose] public section

/-!
The maximum principle and positive source loads for a continuous-coefficient
edge, proved by monotonicity and positive integrals. These are the missing
sign facts needed to connect the edge reconstruction to the finite vertex
system; they are not assumed in EdgeEquation.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory

theorem EdgeEquation.flux_strictAntiOn {a f u j : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (hfpos : ∀ x ∈ Ioo l r, 0 < f x) :
    StrictAntiOn j (Icc l r) := by
  apply strictAntiOn_of_deriv_neg (convex_Icc l r) h.flux_continuous
  intro x hx
  rw [interior_Icc] at hx
  rw [(h.flux_derivative x hx).deriv]
  linarith [hfpos x hx]

/-- A positive source puts every interior state value strictly above the
smaller endpoint value, without differentiating a. -/
theorem EdgeEquation.state_gt_min {a f u j : ℝ → ℝ} {l r x : ℝ}
    (h : EdgeEquation a f l r u j)
    (hapos : ∀ y ∈ Icc l r, 0 < a y) (hfpos : ∀ y ∈ Ioo l r, 0 < f y)
    (hx : x ∈ Ioo l r) : min (u l) (u r) < u x := by
  have hanti := h.flux_strictAntiOn hfpos
  have hxI : x ∈ Icc l r := ⟨hx.1.le, hx.2.le⟩
  by_cases hsign : 0 ≤ j x
  · have hinc : StrictMonoOn u (Icc l x) := by
      apply strictMonoOn_of_deriv_pos (convex_Icc l x)
        (h.state_continuous.mono (Icc_subset_Icc le_rfl hx.2.le))
      intro y hy
      rw [interior_Icc] at hy
      have hyI : y ∈ Icc l r := ⟨hy.1.le, (hy.2.trans hx.2).le⟩
      rw [(h.state_derivative y ⟨hy.1, hy.2.trans hx.2⟩).deriv]
      have hj := hanti hyI hxI hy.2
      exact div_pos (by linarith) (hapos y hyI)
    exact lt_of_le_of_lt (min_le_left _ _)
      (hinc ⟨le_rfl, hx.1.le⟩ ⟨hx.1.le, le_rfl⟩ hx.1)
  · have hsign' : j x < 0 := lt_of_not_ge hsign
    have hdec : StrictAntiOn u (Icc x r) := by
      apply strictAntiOn_of_deriv_neg (convex_Icc x r)
        (h.state_continuous.mono (Icc_subset_Icc hx.1.le le_rfl))
      intro y hy
      rw [interior_Icc] at hy
      have hyI : y ∈ Icc l r := ⟨(hx.1.trans hy.1).le, hy.2.le⟩
      rw [(h.state_derivative y ⟨hx.1.trans hy.1, hy.2⟩).deriv]
      have hj := hanti hxI hyI hy.1
      exact div_neg_of_neg_of_pos (by linarith) (hapos y hyI)
    exact lt_of_le_of_lt (min_le_right _ _)
      (hdec ⟨le_rfl, hx.2.le⟩ ⟨hx.2.le, le_rfl⟩ hx.2)

theorem EdgeEquation.state_interior_pos {a f u j : ℝ → ℝ} {l r x : ℝ}
    (h : EdgeEquation a f l r u j)
    (hapos : ∀ y ∈ Icc l r, 0 < a y) (hfpos : ∀ y ∈ Ioo l r, 0 < f y)
    (hleft : 0 ≤ u l) (hright : 0 ≤ u r) (hx : x ∈ Ioo l r) : 0 < u x :=
  lt_of_le_of_lt (le_min hleft hright) (h.state_gt_min hapos hfpos hx)

theorem EdgeEquation.state_pos {a f u j : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j)
    (hapos : ∀ y ∈ Icc l r, 0 < a y) (hfpos : ∀ y ∈ Ioo l r, 0 < f y)
    (hleft : 0 < u l) (hright : 0 < u r) : ∀ x ∈ Icc l r, 0 < u x := by
  intro x hx
  by_cases hxl : x = l
  · simpa only [hxl] using hleft
  by_cases hxr : x = r
  · simpa only [hxr] using hright
  exact h.state_interior_pos hapos hfpos hleft.le hright.le
    ⟨lt_of_le_of_ne hx.1 (Ne.symm hxl), lt_of_le_of_ne hx.2 hxr⟩

noncomputable def leftSourceLoad (a f : ℝ → ℝ) (l r : ℝ) : ℝ :=
  sourcePotential a f l r / resistancePrimitive a l r

noncomputable def rightSourceLoad (a f : ℝ → ℝ) (l r : ℝ) : ℝ :=
  sourcePrimitive f l r - leftSourceLoad a f l r

theorem source_loads_sum (a f : ℝ → ℝ) (l r : ℝ) :
    leftSourceLoad a f l r + rightSourceLoad a f l r = sourcePrimitive f l r := by
  unfold rightSourceLoad
  ring

/-- The exact two endpoint fluxes have the affine form used in a weighted
graph Laplacian. Each edge contributes its own two source loads. -/
theorem edge_endpoint_fluxes (a f : ℝ → ℝ) (l r u₀ u₁ : ℝ) :
    edgeFlux a f l r u₀ u₁ l =
        (u₁ - u₀) / resistancePrimitive a l r + leftSourceLoad a f l r ∧
    edgeFlux a f l r u₀ u₁ r =
        (u₁ - u₀) / resistancePrimitive a l r - rightSourceLoad a f l r := by
  constructor
  · unfold edgeFlux
    rw [show sourcePrimitive f l l = 0 by simp [sourcePrimitive]]
    simp only [sub_zero, edgeInitialFlux, leftSourceLoad, add_div]
  · unfold edgeFlux edgeInitialFlux rightSourceLoad leftSourceLoad
    rw [add_div]
    ring

/-- Both endpoint loads are strictly positive for a positive continuous source. -/
theorem source_loads_pos {a f : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (ha : ContinuousOn a (Icc l r)) (hf : ContinuousOn f (Icc l r))
    (hapos : ∀ x ∈ Icc l r, 0 < a x) (hfpos : ∀ x ∈ Icc l r, 0 < f x) :
    0 < leftSourceLoad a f l r ∧ 0 < rightSourceLoad a f l r := by
  have hane : ∀ x ∈ Icc l r, a x ≠ 0 := fun x hx => ne_of_gt (hapos x hx)
  have hR := resistance_pos hlr ha hapos
  have hF := sourcePrimitive_continuousOn hlr.le hf
  have hmono : StrictMonoOn (sourcePrimitive f l) (Icc l r) :=
    integral_primitive_strictMonoOn hlr.le hf (fun x hx => hfpos x ⟨hx.1.le, hx.2.le⟩)
  have hzero : sourcePrimitive f l l = 0 := by simp [sourcePrimitive]
  have hl : l ∈ Icc l r := ⟨le_rfl, hlr.le⟩
  have hr : r ∈ Icc l r := ⟨hlr.le, le_rfl⟩
  have hmass : 0 < sourcePrimitive f l r := by
    simpa only [hzero] using hmono hl hr hlr
  have hbetween : ∀ x ∈ Icc l r,
      0 ≤ sourcePrimitive f l x ∧ sourcePrimitive f l x ≤ sourcePrimitive f l r := by
    intro x hx
    constructor
    · simpa only [hzero] using hmono.monotoneOn hl hx hx.1
    · exact hmono.monotoneOn hx hr hx.2
  have hQ : 0 < sourcePotential a f l r := by
    apply intervalIntegral.integral_pos hlr (hF.div ha hane)
    · intro x hx
      exact div_nonneg (hbetween x ⟨hx.1.le, hx.2⟩).1 (hapos x ⟨hx.1.le, hx.2⟩).le
    · exact ⟨r, hr, div_pos hmass (hapos r hr)⟩
  have hcomp : 0 < ∫ x in l..r, (sourcePrimitive f l r - sourcePrimitive f l x) / a x := by
    apply intervalIntegral.integral_pos hlr ((continuousOn_const.sub hF).div ha hane)
    · intro x hx
      exact div_nonneg (sub_nonneg.mpr (hbetween x ⟨hx.1.le, hx.2⟩).2)
        (hapos x ⟨hx.1.le, hx.2⟩).le
    · refine ⟨l, hl, ?_⟩
      change 0 < (sourcePrimitive f l r - sourcePrimitive f l l) / a l
      rw [hzero, sub_zero]
      exact div_pos hmass (hapos l hl)
  have hcomp_eq : (∫ x in l..r, (sourcePrimitive f l r - sourcePrimitive f l x) / a x) =
      sourcePrimitive f l r * resistancePrimitive a l r - sourcePotential a f l r := by
    have hiR : IntervalIntegrable (fun x => sourcePrimitive f l r * (1 / a x)) volume l r :=
      (continuousOn_const.mul (continuousOn_const.div ha hane)).intervalIntegrable_of_Icc hlr.le
    have hiQ : IntervalIntegrable (fun x => sourcePrimitive f l x / a x) volume l r :=
      (hF.div ha hane).intervalIntegrable_of_Icc hlr.le
    calc
      _ = ∫ x in l..r, (sourcePrimitive f l r * (1 / a x) - sourcePrimitive f l x / a x) := by
        apply intervalIntegral.integral_congr
        intro x _
        dsimp only
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub hiR hiQ, intervalIntegral.integral_const_mul]
        rfl
  refine ⟨div_pos hQ hR, ?_⟩
  unfold rightSourceLoad leftSourceLoad
  apply sub_pos.mpr
  apply (div_lt_iff₀ hR).mpr
  rw [hcomp_eq] at hcomp
  linarith

end TimeTraps.Analysis
