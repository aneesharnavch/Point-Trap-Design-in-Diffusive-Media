module

public import TimeTraps.Spectral.DirichletState

@[expose] public section

/-!
Identification and attainment of the independently defined Dirichlet and
mixed Rayleigh infima. All competitors are original physical H1 functions
with precisely the selected absorbing traces.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

theorem DirichletInterval.groundState_positive (P : DirichletInterval) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) P.length) : 0 < P.groundState x := by
  have hl : -(Real.pi / 2) ≤ P.waveNumber * (0 - P.center) := by
    rw [P.groundPhase_left]
    cases P.ends <;> dsimp <;> linarith [Real.pi_pos]
  have hr : P.waveNumber * (P.length - P.center) ≤ Real.pi / 2 := by
    rw [P.groundPhase_right]
    cases P.ends <;> dsimp <;> linarith [Real.pi_pos]
  apply Real.cos_pos_of_mem_Ioo
  constructor <;> nlinarith [mul_pos P.waveNumber_pos hx.1,
    mul_pos P.waveNumber_pos (sub_pos.mpr hx.2)]

theorem DirichletInterval.quadraticForm_lower (P : DirichletInterval) {v : ℝ → ℝ}
    (hv : P.admissible v) :
    P.diffusivity * P.waveNumber ^ 2 * P.squareMass v ≤ P.quadraticForm v := by
  have h : P.waveNumber ^ 2 * P.squareMass v ≤
      ∫ x in (0 : ℝ)..P.length, deriv v x ^ 2 := by
    cases he : P.ends with
    | left =>
      have ht : v 0 = 0 := by simpa only [zeroTraces, he] using hv.2
      simpa only [waveNumber, he, squareMass] using
        dirichlet_neumann_poincare P.length_pos hv.1 ht
    | right =>
      have ht : v P.length = 0 := by simpa only [zeroTraces, he] using hv.2
      simpa only [waveNumber, he, squareMass] using
        neumann_dirichlet_poincare P.length_pos hv.1 ht
    | both =>
      have ht : v 0 = 0 ∧ v P.length = 0 := by simpa only [zeroTraces, he] using hv.2
      simpa only [waveNumber, he, squareMass] using
        dirichlet_poincare P.length_pos hv.1 ht.1 ht.2
  simpa only [quadraticForm, mul_assoc] using mul_le_mul_of_nonneg_left h P.diffusivity_pos.le

theorem DirichletInterval.groundState_rayleigh_member (P : DirichletInterval) :
    P.diffusivity * P.waveNumber ^ 2 ∈ P.rayleighValues := by
  refine ⟨P.groundState, P.groundState_admissible, P.groundState_mass_pos, ?_⟩
  rw [P.groundState_weak.self_quadraticForm,
    mul_div_cancel_right₀ _ P.groundState_mass_pos.ne']

theorem DirichletInterval.rayleighValues_nonempty (P : DirichletInterval) :
    P.rayleighValues.Nonempty := ⟨_, P.groundState_rayleigh_member⟩

theorem DirichletInterval.rayleigh_lower (P : DirichletInterval) {r : ℝ}
    (hr : r ∈ P.rayleighValues) : P.diffusivity * P.waveNumber ^ 2 ≤ r := by
  obtain ⟨v, hv, hm, rfl⟩ := hr
  exact (le_div_iff₀ hm).mpr (P.quadraticForm_lower hv)

theorem DirichletInterval.principalValue_eq (P : DirichletInterval) :
    P.principalValue = P.diffusivity * P.waveNumber ^ 2 :=
  le_antisymm (csInf_le P.rayleighValues_bddBelow P.groundState_rayleigh_member)
    (le_csInf P.rayleighValues_nonempty (fun _ hr => P.rayleigh_lower hr))

theorem DirichletInterval.rayleigh_minimum (P : DirichletInterval) :
    IsLeast P.rayleighValues (P.diffusivity * P.waveNumber ^ 2) :=
  ⟨P.groundState_rayleigh_member, fun _ hr => P.rayleigh_lower hr⟩

theorem DirichletInterval.principalValue_pos (P : DirichletInterval) : 0 < P.principalValue := by
  rw [P.principalValue_eq]
  exact mul_pos P.diffusivity_pos (sq_pos_of_pos P.waveNumber_pos)

theorem DirichletInterval.principal_ground_state (P : DirichletInterval) :
    DirichletWeakEigenEquation P P.principalValue P.groundState := by
  rw [P.principalValue_eq]
  exact P.groundState_weak

theorem DirichletInterval.principalValue_both (P : DirichletInterval) (he : P.ends = .both) :
    P.principalValue = P.diffusivity * Real.pi ^ 2 / P.length ^ 2 := by
  rw [P.principalValue_eq]
  simp only [waveNumber, he, div_pow, mul_div_assoc]

theorem DirichletInterval.principalValue_left (P : DirichletInterval) (he : P.ends = .left) :
    P.principalValue = P.diffusivity * Real.pi ^ 2 / (4 * P.length ^ 2) := by
  rw [P.principalValue_eq]
  simp only [waveNumber, he, div_pow, mul_pow, mul_div_assoc]
  norm_num

theorem DirichletInterval.principalValue_right (P : DirichletInterval) (he : P.ends = .right) :
    P.principalValue = P.diffusivity * Real.pi ^ 2 / (4 * P.length ^ 2) := by
  rw [P.principalValue_eq]
  simp only [waveNumber, he, div_pow, mul_pow, mul_div_assoc]
  norm_num

end TimeTraps.Spectral
