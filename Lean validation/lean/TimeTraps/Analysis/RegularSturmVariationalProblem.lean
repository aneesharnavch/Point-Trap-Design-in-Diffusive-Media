module

public import TimeTraps.Analysis.RegularSturmSpectrumEquivalence

@[expose] public section

/-! The independent regular variable-coefficient Sturm Rayleigh class contains all
actual physical AC/L2 functions with the selected zero traces and positive
speed-weighted square mass. Its definition uses neither eigenvalues nor operator domains.
A polynomial competitor proves nonemptiness directly. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def RegularSturmProblem.quadraticForm
    (P : RegularSturmProblem ι l r) (u : ℝ → ℝ) : ℝ :=
  regularSturmPhysicalForm P.conductance P.potential P.strength P.site l r u u

noncomputable def RegularSturmProblem.squareMass
    (P : RegularSturmProblem ι l r) (u : ℝ → ℝ) : ℝ := ∫ x in l..r, P.speed x * u x ^ 2

def RegularSturmProblem.rayleighValues (P : RegularSturmProblem ι l r) : Set ℝ :=
  {q | ∃ u : ℝ → ℝ, IntervalEnergy u l r ∧
    (∀ x ∈ P.boundary.zero_sites, u x = 0) ∧ 0 < P.squareMass u ∧
      q = P.quadraticForm u / P.squareMass u}

noncomputable def RegularSturmProblem.principalValue (P : RegularSturmProblem ι l r) : ℝ :=
  sInf P.rayleighValues

theorem RegularSturmProblem.squareMass_congr (P : RegularSturmProblem ι l r)
    {u v : ℝ → ℝ} (huv : EqOn u v (Icc l r)) : P.squareMass u = P.squareMass v := by
  apply intervalIntegral.integral_congr_Ioo_of_le P.boundary.interval_pos.le
  intro x hx
  change P.speed x * u x ^ 2 = P.speed x * v x ^ 2
  rw [huv (Ioo_subset_Icc_self hx)]

theorem RegularSturmProblem.squareMass_representative (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) :
    P.squareMass (u.val.representative P.boundary.interval_pos) = ‖P.stateL u‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, P.stateL_inner]
  simp only [squareMass, pow_two, mul_assoc]

theorem RegularSturmProblem.squareMass_ofEnergy (P : RegularSturmProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    ‖P.stateL (P.boundary.ofEnergy hu huz)‖ ^ 2 = P.squareMass u := by
  rw [← P.squareMass_representative]
  exact P.squareMass_congr (P.boundary.ofEnergy_representative hu huz)

theorem RegularSturmProblem.quadraticForm_representative (P : RegularSturmProblem ι l r)
    (u : IntervalSeparatedSpace P.boundary) :
    P.quadraticForm (u.val.representative P.boundary.interval_pos) = P.form u u :=
  (P.form_apply u u).symm

theorem RegularSturmProblem.quadraticForm_ofEnergy (P : RegularSturmProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) (huz : ∀ x ∈ P.boundary.zero_sites, u x = 0) :
    P.form (P.boundary.ofEnergy hu huz) (P.boundary.ofEnergy hu huz) = P.quadraticForm u :=
  P.form_ofEnergy hu hu huz huz

theorem RegularSturmProblem.rayleighValues_nonempty (P : RegularSturmProblem ι l r) :
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
    have hi : IntervalIntegrable (fun x => P.speed x * u x ^ 2) volume l r := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le P.boundary.interval_pos.le]
      exact P.speed_continuous.mul ((by fun_prop : Continuous u).continuousOn.pow 2)
    exact intervalIntegral.intervalIntegral_pos_of_pos_on hi
      (fun x hx => mul_pos (P.speed_pos x (Ioo_subset_Icc_self hx))
        (sq_pos_of_pos (mul_pos (sub_pos.mpr hx.1) (sub_pos.mpr hx.2)))) P.boundary.interval_pos
  exact ⟨_, u, hu, huz, hm, rfl⟩

theorem RegularSturmProblem.rayleighValues_bddBelow (P : RegularSturmProblem ι l r) :
    BddBelow P.rayleighValues := by
  refine ⟨-P.massShift, ?_⟩
  rintro q ⟨u, hu, huz, hm, rfl⟩
  apply (le_div_iff₀ hm).mpr
  have h := P.form_semibounded (P.boundary.ofEnergy hu huz)
  rw [P.squareMass_ofEnergy hu huz, P.quadraticForm_ofEnergy hu huz] at h
  simpa only [neg_mul] using h

end TimeTraps.Analysis
