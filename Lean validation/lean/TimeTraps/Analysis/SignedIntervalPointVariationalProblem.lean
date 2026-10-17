module

public import TimeTraps.Analysis.SignedIntervalPointPhysical

@[expose] public section

/-! The signed interval Rayleigh class is defined from all actual physical
H1 functions of positive square mass. Its definition uses the original
point form and makes no reference to eigenvalues or the operator domain. -/

namespace TimeTraps.Analysis

open Set MeasureTheory IntervalSobolevSpace

variable {ι : Type*} [Fintype ι] {l r : ℝ}

noncomputable def SignedIntervalPointProblem.quadraticForm
    (P : SignedIntervalPointProblem ι l r) (u : ℝ → ℝ) : ℝ :=
  intervalPointForm P.diffusivity P.strength P.site l r u u

noncomputable def SignedIntervalPointProblem.squareMass
    (_P : SignedIntervalPointProblem ι l r) (u : ℝ → ℝ) : ℝ := ∫ x in l..r, u x ^ 2

def SignedIntervalPointProblem.rayleighValues (P : SignedIntervalPointProblem ι l r) : Set ℝ :=
  {q | ∃ u : ℝ → ℝ, IntervalEnergy u l r ∧ 0 < P.squareMass u ∧
    q = P.quadraticForm u / P.squareMass u}

noncomputable def SignedIntervalPointProblem.principalValue (P : SignedIntervalPointProblem ι l r) : ℝ :=
  sInf P.rayleighValues

theorem SignedIntervalPointProblem.squareMass_congr (P : SignedIntervalPointProblem ι l r)
    {u v : ℝ → ℝ} (huv : EqOn u v (Icc l r)) : P.squareMass u = P.squareMass v := by
  apply intervalIntegral.integral_congr_Ioo_of_le P.interval_pos.le
  intro x hx
  change u x ^ 2 = v x ^ 2
  rw [huv (Ioo_subset_Icc_self hx)]

theorem SignedIntervalPointProblem.squareMass_representative (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) : P.squareMass (u.representative P.interval_pos) = ‖u.state‖ ^ 2 := by
  rw [squareMass, ← real_inner_self_eq_norm_sq, state_inner u u P.interval_pos]
  simp only [pow_two]

theorem SignedIntervalPointProblem.squareMass_ofEnergy (P : SignedIntervalPointProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    ‖(ofEnergy hu P.interval_pos).state‖ ^ 2 = P.squareMass u := by
  rw [← P.squareMass_representative]
  exact P.squareMass_congr (representative_ofEnergy hu P.interval_pos)

theorem SignedIntervalPointProblem.quadraticForm_representative (P : SignedIntervalPointProblem ι l r)
    (u : IntervalSobolevSpace l r) :
    P.quadraticForm (u.representative P.interval_pos) = P.form u u :=
  (intervalSobolevPointForm_apply P.interval_pos P.diffusivity P.strength P.site P.site_mem u u).symm

theorem SignedIntervalPointProblem.quadraticForm_ofEnergy (P : SignedIntervalPointProblem ι l r)
    {u : ℝ → ℝ} (hu : IntervalEnergy u l r) :
    P.form (ofEnergy hu P.interval_pos) (ofEnergy hu P.interval_pos) = P.quadraticForm u :=
  intervalSobolevPointForm_ofEnergy P.interval_pos P.diffusivity P.strength P.site P.site_mem hu hu

theorem SignedIntervalPointProblem.rayleighValues_nonempty (P : SignedIntervalPointProblem ι l r) :
    P.rayleighValues.Nonempty := by
  have hm : 0 < P.squareMass (fun _ => 1) := by
    change 0 < ∫ _x in l..r, (1 : ℝ) ^ 2
    simp only [one_pow, intervalIntegral.integral_const, smul_eq_mul, mul_one]
    exact sub_pos.mpr P.interval_pos
  exact ⟨_, (fun _ => 1), IntervalEnergy.const 1 l r, hm, rfl⟩

theorem SignedIntervalPointProblem.rayleighValues_bddBelow (P : SignedIntervalPointProblem ι l r) :
    BddBelow P.rayleighValues := by
  refine ⟨-intervalPointNegativeBound P.diffusivity P.strength l r, ?_⟩
  rintro q ⟨u, hu, hm, rfl⟩
  apply (le_div_iff₀ hm).mpr
  simpa only [quadraticForm, squareMass, neg_mul] using
    hu.point_form_semibounded P.interval_pos P.diffusivity_pos P.strength P.site P.site_mem

end TimeTraps.Analysis
