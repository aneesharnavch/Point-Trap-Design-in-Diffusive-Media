module

public import TimeTraps.Analysis.IntervalCalculus
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Positivity

@[expose] public section

/-!
Exact Dirichlet reconstruction for -(a u')' = f on one edge. The coefficient
and source are only continuous on the closed edge. The flux is a separate
function, so no derivative of a is required. Uniqueness is equality on the
edge, not equality of arbitrary extensions outside it.
-/

namespace TimeTraps.Analysis

open Set MeasureTheory

noncomputable def sourcePrimitive (f : ℝ → ℝ) (l x : ℝ) : ℝ :=
  ∫ t in l..x, f t

noncomputable def resistancePrimitive (a : ℝ → ℝ) (l x : ℝ) : ℝ :=
  ∫ t in l..x, 1 / a t

noncomputable def sourcePotential (a f : ℝ → ℝ) (l x : ℝ) : ℝ :=
  ∫ t in l..x, sourcePrimitive f l t / a t

noncomputable def edgeInitialFlux (a f : ℝ → ℝ) (l r u₀ u₁ : ℝ) : ℝ :=
  (u₁ - u₀ + sourcePotential a f l r) / resistancePrimitive a l r

noncomputable def edgeFlux (a f : ℝ → ℝ) (l r u₀ u₁ x : ℝ) : ℝ :=
  edgeInitialFlux a f l r u₀ u₁ - sourcePrimitive f l x

noncomputable def edgeState (a f : ℝ → ℝ) (l r u₀ u₁ x : ℝ) : ℝ :=
  u₀ + edgeInitialFlux a f l r u₀ u₁ * resistancePrimitive a l x -
    sourcePotential a f l x

/-- A strong edge equation in state/flux variables. It assumes neither an
integral representation, conservation, positivity, nor existence. -/
structure EdgeEquation (a f : ℝ → ℝ) (l r : ℝ) (u j : ℝ → ℝ) : Prop where
  state_continuous : ContinuousOn u (Icc l r)
  flux_continuous : ContinuousOn j (Icc l r)
  state_derivative : ∀ x ∈ Ioo l r, HasDerivAt u (j x / a x) x
  flux_derivative : ∀ x ∈ Ioo l r, HasDerivAt j (-f x) x

theorem sourcePrimitive_continuousOn {f : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (hf : ContinuousOn f (Icc l r)) :
    ContinuousOn (sourcePrimitive f l) (Icc l r) :=
  integral_primitive_continuousOn hlr hf

theorem resistancePrimitive_continuousOn {a : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (ha : ContinuousOn a (Icc l r)) (hane : ∀ x ∈ Icc l r, a x ≠ 0) :
    ContinuousOn (resistancePrimitive a l) (Icc l r) :=
  integral_primitive_continuousOn hlr (continuousOn_const.div ha hane)

theorem sourcePotential_continuousOn {a f : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (ha : ContinuousOn a (Icc l r)) (hf : ContinuousOn f (Icc l r))
    (hane : ∀ x ∈ Icc l r, a x ≠ 0) :
    ContinuousOn (sourcePotential a f l) (Icc l r) :=
  integral_primitive_continuousOn hlr
    ((sourcePrimitive_continuousOn hlr hf).div ha hane)

theorem resistance_pos {a : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (ha : ContinuousOn a (Icc l r))
    (hapos : ∀ x ∈ Icc l r, 0 < a x) :
    0 < resistancePrimitive a l r := by
  apply intervalIntegral.integral_pos hlr
    (continuousOn_const.div ha (fun x hx => ne_of_gt (hapos x hx)))
  · intro x hx
    exact (one_div_pos.mpr (hapos x ⟨hx.1.le, hx.2⟩)).le
  · exact ⟨l, ⟨le_rfl, hlr.le⟩, one_div_pos.mpr (hapos l ⟨le_rfl, hlr.le⟩)⟩

theorem edgeState_left (a f : ℝ → ℝ) (l r u₀ u₁ : ℝ) :
    edgeState a f l r u₀ u₁ l = u₀ := by
  simp [edgeState, resistancePrimitive, sourcePotential]

theorem edgeState_right (a f : ℝ → ℝ) (l r u₀ u₁ : ℝ)
    (hR : resistancePrimitive a l r ≠ 0) :
    edgeState a f l r u₀ u₁ r = u₁ := by
  unfold edgeState edgeInitialFlux
  rw [div_mul_cancel₀ _ hR]
  ring

/-- The integral formula actually satisfies the state and flux differential equations. -/
theorem reconstructed_edge_equation {a f : ℝ → ℝ} {l r : ℝ}
    (hlr : l ≤ r) (ha : ContinuousOn a (Icc l r)) (hf : ContinuousOn f (Icc l r))
    (hane : ∀ x ∈ Icc l r, a x ≠ 0) (u₀ u₁ : ℝ) :
    EdgeEquation a f l r (edgeState a f l r u₀ u₁) (edgeFlux a f l r u₀ u₁) := by
  have hF := sourcePrimitive_continuousOn hlr hf
  have hR := resistancePrimitive_continuousOn hlr ha hane
  have hQ := sourcePotential_continuousOn hlr ha hf hane
  have hinv : ContinuousOn (fun x => 1 / a x) (Icc l r) := continuousOn_const.div ha hane
  have hFa : ContinuousOn (fun x => sourcePrimitive f l x / a x) (Icc l r) := hF.div ha hane
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (continuousOn_const.add (continuousOn_const.mul hR)).sub hQ
  · exact continuousOn_const.sub hF
  · intro x hx
    have hdR := integral_primitive_hasDerivAt hinv hx
    have hdQ := integral_primitive_hasDerivAt hFa hx
    convert! ((hdR.const_mul (edgeInitialFlux a f l r u₀ u₁)).const_add u₀).sub hdQ using 1
    simp only [edgeFlux]
    ring
  · intro x hx
    convert! (integral_primitive_hasDerivAt hf hx).const_sub (edgeInitialFlux a f l r u₀ u₁) using 1

/-- Conservation on every subedge follows from the differential equation. -/
theorem EdgeEquation.flux_formula {a f u j : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (hf : ContinuousOn f (Icc l r))
    {x : ℝ} (hx : x ∈ Icc l r) :
    j x = j l - sourcePrimitive f l x := by
  have hid := integral_derivative_to_point h.flux_continuous hf.neg h.flux_derivative hx
  simp only [Pi.neg_apply, intervalIntegral.integral_neg] at hid
  change -sourcePrimitive f l x = j x - j l at hid
  linarith

/-- Every solution has the integral representation; this is not a field of the model. -/
theorem EdgeEquation.state_formula {a f u j : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (ha : ContinuousOn a (Icc l r))
    (hf : ContinuousOn f (Icc l r)) (hane : ∀ x ∈ Icc l r, a x ≠ 0)
    {x : ℝ} (hx : x ∈ Icc l r) :
    u x = u l + j l * resistancePrimitive a l x - sourcePotential a f l x := by
  have hsub : Icc l x ⊆ Icc l r := Icc_subset_Icc le_rfl hx.2
  have hiR : IntervalIntegrable (fun t => 1 / a t) volume l x :=
    ((continuousOn_const.div ha hane).mono hsub).intervalIntegrable_of_Icc hx.1
  have hiQ : IntervalIntegrable (fun t => sourcePrimitive f l t / a t) volume l x :=
    (((sourcePrimitive_continuousOn (hx.1.trans hx.2) hf).div ha hane).mono hsub).intervalIntegrable_of_Icc hx.1
  have hja := h.flux_continuous.div ha hane
  have hid := integral_derivative_to_point h.state_continuous hja h.state_derivative hx
  have hrep : (∫ t in l..x, j t / a t) =
      j l * resistancePrimitive a l x - sourcePotential a f l x := by
    calc
      _ = ∫ t in l..x, (j l * (1 / a t) - sourcePrimitive f l t / a t) := by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc l r := hsub (by simpa only [uIcc_of_le hx.1] using ht)
        change j t / a t = j l * (1 / a t) - sourcePrimitive f l t / a t
        rw [h.flux_formula hf ht']
        ring
      _ = _ := by
        rw [intervalIntegral.integral_sub]
        · rw [intervalIntegral.integral_const_mul]
          rfl
        · exact hiR.const_mul (j l)
        · exact hiQ
  simp only [Pi.div_apply] at hid
  rw [hrep] at hid
  linarith

/-- The endpoint values determine the initial flux uniquely. -/
theorem EdgeEquation.initial_flux {a f u j : ℝ → ℝ} {l r : ℝ}
    (h : EdgeEquation a f l r u j) (hlr : l ≤ r)
    (ha : ContinuousOn a (Icc l r)) (hf : ContinuousOn f (Icc l r))
    (hane : ∀ x ∈ Icc l r, a x ≠ 0) (hR : resistancePrimitive a l r ≠ 0) :
    j l = edgeInitialFlux a f l r (u l) (u r) := by
  have hid := h.state_formula ha hf hane ⟨hlr, le_rfl⟩
  unfold edgeInitialFlux
  apply (eq_div_iff hR).mpr
  linarith

/-- Uniqueness for the physical edge, independent of extensions outside it. -/
theorem edge_solution_unique {a f u j v k : ℝ → ℝ} {l r : ℝ}
    (hu : EdgeEquation a f l r u j) (hv : EdgeEquation a f l r v k)
    (hlr : l < r) (ha : ContinuousOn a (Icc l r)) (hf : ContinuousOn f (Icc l r))
    (hapos : ∀ x ∈ Icc l r, 0 < a x) (hleft : u l = v l) (hright : u r = v r) :
    EqOn u v (Icc l r) ∧ EqOn j k (Icc l r) := by
  have hane : ∀ x ∈ Icc l r, a x ≠ 0 := fun x hx => ne_of_gt (hapos x hx)
  have hR := ne_of_gt (resistance_pos hlr ha hapos)
  have hjk : j l = k l := by
    rw [hu.initial_flux hlr.le ha hf hane hR, hv.initial_flux hlr.le ha hf hane hR,
      hleft, hright]
  constructor
  · intro x hx
    rw [hu.state_formula ha hf hane hx, hv.state_formula ha hf hane hx, hleft, hjk]
  · intro x hx
    rw [hu.flux_formula hf hx, hv.flux_formula hf hx, hjk]

/-- Existence with arbitrary Dirichlet data and uniqueness on the closed edge. -/
theorem edge_solution_exists_unique_on {a f : ℝ → ℝ} {l r : ℝ}
    (hlr : l < r) (ha : ContinuousOn a (Icc l r)) (hf : ContinuousOn f (Icc l r))
    (hapos : ∀ x ∈ Icc l r, 0 < a x) (u₀ u₁ : ℝ) :
    ∃ u j : ℝ → ℝ, EdgeEquation a f l r u j ∧ u l = u₀ ∧ u r = u₁ ∧
      ∀ v k, EdgeEquation a f l r v k → v l = u₀ → v r = u₁ →
        EqOn v u (Icc l r) ∧ EqOn k j (Icc l r) := by
  have hane : ∀ x ∈ Icc l r, a x ≠ 0 := fun x hx => ne_of_gt (hapos x hx)
  have hR := ne_of_gt (resistance_pos hlr ha hapos)
  have heq := reconstructed_edge_equation hlr.le ha hf hane u₀ u₁
  refine ⟨edgeState a f l r u₀ u₁, edgeFlux a f l r u₀ u₁, heq,
    edgeState_left a f l r u₀ u₁, edgeState_right a f l r u₀ u₁ hR, ?_⟩
  intro v k hv hv₀ hv₁
  apply edge_solution_unique hv heq hlr ha hf hapos
  · rw [hv₀, edgeState_left]
  · rw [hv₁, edgeState_right a f l r u₀ u₁ hR]

end TimeTraps.Analysis
