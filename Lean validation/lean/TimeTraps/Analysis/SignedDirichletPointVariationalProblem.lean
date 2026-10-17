module

public import TimeTraps.Analysis.SignedDirichletPointPhysical

@[expose] public section

/-! The independent signed Dirichlet/mixed Rayleigh class contains all
actual physical AC/L2 functions with the selected zero traces and positive
square mass. Its definition uses neither eigenvalues nor operator domains.
A polynomial competitor proves nonemptiness directly. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def SignedDirichletPointProblem.quadraticForm
    (P : SignedDirichletPointProblem ι l r) (u : ℝ → ℝ) : ℝ :=
  intervalPointForm P.diffusivity P.strength P.site l r u u

noncomputable def SignedDirichletPointProblem.squareMass
    (_P : SignedDirichletPointProblem ι l r) (u : ℝ → ℝ) : ℝ := ∫ x in l..r, u x ^ 2

def SignedDirichletPointProblem.rayleighValues (P : SignedDirichletPointProblem ι l r) : Set ℝ :=
  {q | ∃ u : ℝ → ℝ, IntervalEnergy u l r ∧
    (∀ x ∈ P.boundary.zero_sites, u x = 0) ∧ 0 < P.squareMass u ∧
      q = P.quadraticForm u / P.squareMass u}

noncomputable def SignedDirichletPointProblem.principalValue (P : SignedDirichletPointProblem ι l r) : ℝ :=
  sInf P.rayleighValues

theorem SignedDirichletPointProblem.squareMass_congr (P : SignedDirichletPointProblem ι l r)
    {u v : ℝ → ℝ} (huv : EqOn u v (Icc l r)) : P.squareMass u = P.squareMass v := by
  apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
  intro x hx
  change u x ^ 2 = v x ^ 2
  rw [huv (Ioo_subset_Icc_self hx)]

theorem SignedDirichletPointProblem.squareMass_representative (P : SignedDirichletPointProblem ι l r)
    (u : IntervalDirichletSpace P.boundary) :
    P.squareMass (u.val.representative P.boundary.interval_pos) = ‖P.boundary.stateL u‖ ^ 2 := by
  change (∫ x in l..r, u.val.representative P.boundary.interval_pos x ^ 2) = ‖u.val.state‖ ^ 2
  rw [← real_inner_self_eq_norm_sq, state_inner u.val u.val P.boundary.interval_pos]
  simp only [pow_two]

theorem SignedDirichletPointProblem.squareMass_ofEnergy (P : SignedDirichletPointProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    ‖P.boundary.stateL (P.boundary.ofEnergy hu huz)‖ ^ 2 = P.squareMass u := by
  rw [← P.squareMass_representative]
  exact P.squareMass_congr (P.boundary.ofEnergy_representative hu huz)

theorem SignedDirichletPointProblem.quadraticForm_representative (P : SignedDirichletPointProblem ι l r)
    (u : IntervalDirichletSpace P.boundary) :
    P.quadraticForm (u.val.representative P.boundary.interval_pos) = P.form u u :=
  (intervalDirichletPointForm_apply P.boundary P.diffusivity P.strength P.site P.site_mem u u).symm

theorem SignedDirichletPointProblem.quadraticForm_ofEnergy (P : SignedDirichletPointProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    P.form (P.boundary.ofEnergy hu huz) (P.boundary.ofEnergy hu huz) = P.quadraticForm u :=
  intervalDirichletPointForm_ofEnergy P.boundary P.diffusivity P.strength P.site P.site_mem hu hu huz huz

theorem SignedDirichletPointProblem.rayleighValues_nonempty (P : SignedDirichletPointProblem ι l r) :
    P.rayleighValues.Nonempty := by
  let u : ℝ → ℝ := fun x => (x - l) * (r - x)
  have hu : IntervalEnergy u l r := by
    apply intervalEnergy_of_continuous_derivative (g := fun x => 1 * (r - x) + (x - l) * (0 - 1))
      P.boundary.interval_pos.le
    · fun_prop
    · fun_prop
    · intro x _
      exact ((hasDerivAt_id x).sub_const l).mul ((hasDerivAt_const x r).sub (hasDerivAt_id x))
  have huz : ∀ x ∈ P.boundary.zero_sites, u x = 0 := by
    intro x hx
    rcases P.boundary.boundary_only x hx with rfl | rfl <;> simp only [u, sub_self, zero_mul, mul_zero]
  have hm : 0 < P.squareMass u := by
    apply intervalIntegral.intervalIntegral_pos_of_pos_on hu.state_square_integrable
      (fun x hx => sq_pos_of_pos (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)))
      P.boundary.interval_pos
  exact ⟨_, u, hu, huz, hm, rfl⟩

theorem SignedDirichletPointProblem.rayleighValues_bddBelow (P : SignedDirichletPointProblem ι l r) :
    BddBelow P.rayleighValues := by
  refine ⟨-intervalPointNegativeBound P.diffusivity P.strength l r, ?_⟩
  rintro q ⟨u, hu, _, hm, rfl⟩
  apply (le_div_iff₀ hm).mpr
  simpa only [quadraticForm, squareMass, neg_mul] using
    hu.point_form_semibounded P.boundary.interval_pos P.diffusivity_pos P.strength P.site P.site_mem

end TimeTraps.Analysis
