module

public import TimeTraps.Spectral.DirichletInterval
public import TimeTraps.Spectral.DirichletPoincare
public import TimeTraps.Analysis.EdgeWeak

@[expose] public section

/-!
Explicit first modes on empty absorbing cells, including both mixed
orientations. The mode is shown admissible in the independently defined
space, with positive mass and the full H1 weak equation.
-/

namespace TimeTraps.Spectral

open Set MeasureTheory TimeTraps.Analysis

noncomputable def DirichletInterval.waveNumber (P : DirichletInterval) : ℝ :=
  match P.ends with
  | .both => Real.pi / P.length
  | _ => Real.pi / (2 * P.length)

noncomputable def DirichletInterval.center (P : DirichletInterval) : ℝ :=
  match P.ends with
  | .left => P.length
  | .right => 0
  | .both => P.length / 2

noncomputable def DirichletInterval.groundState (P : DirichletInterval) : ℝ → ℝ :=
  dirichletCosine P.waveNumber P.center

noncomputable def DirichletInterval.groundSlope (P : DirichletInterval) : ℝ → ℝ :=
  dirichletCosineSlope P.waveNumber P.center

theorem DirichletInterval.waveNumber_pos (P : DirichletInterval) : 0 < P.waveNumber := by
  rcases P with ⟨L, hL, D, hD, e⟩
  cases e <;> dsimp [waveNumber] <;> positivity

theorem DirichletInterval.center_mem (P : DirichletInterval) :
    P.center ∈ Icc (0 : ℝ) P.length := by
  rcases P with ⟨L, hL, D, hD, e⟩
  cases e <;> dsimp [center] <;> constructor <;> linarith

theorem DirichletInterval.groundPhase_left (P : DirichletInterval) :
    P.waveNumber * (0 - P.center) =
      match P.ends with | .right => 0 | _ => -(Real.pi / 2) := by
  rcases P with ⟨L, hL, D, hD, e⟩
  cases e <;> dsimp [waveNumber, center] <;> field_simp [hL.ne'] <;> ring

theorem DirichletInterval.groundPhase_right (P : DirichletInterval) :
    P.waveNumber * (P.length - P.center) =
      match P.ends with | .left => 0 | _ => Real.pi / 2 := by
  rcases P with ⟨L, hL, D, hD, e⟩
  cases e <;> dsimp [waveNumber, center] <;> field_simp [hL.ne'] <;> ring

theorem DirichletInterval.groundState_admissible (P : DirichletInterval) :
    P.admissible P.groundState := by
  refine ⟨dirichletCosine_energy _ _ _ _ P.length_pos.le, ?_⟩
  have hl : P.groundState 0 = Real.cos (P.waveNumber * (0 - P.center)) := rfl
  have hr : P.groundState P.length =
      Real.cos (P.waveNumber * (P.length - P.center)) := rfl
  rw [P.groundPhase_left] at hl
  rw [P.groundPhase_right] at hr
  cases he : P.ends <;>
    simp_all [zeroTraces, Real.cos_neg, Real.cos_pi_div_two]

theorem DirichletInterval.groundState_mass_pos (P : DirichletInterval) :
    0 < P.squareMass P.groundState := by
  apply intervalIntegral.integral_pos P.length_pos
    ((dirichletCosine_continuous _ _).continuousOn.pow 2)
  · intro x _
    exact sq_nonneg _
  · refine ⟨P.center, P.center_mem, ?_⟩
    simp [dirichletCosine]

theorem DirichletInterval.groundSlope_boundary (P : DirichletInterval) {v : ℝ → ℝ}
    (hv : P.zeroTraces v) :
    P.groundSlope 0 * v 0 = 0 ∧ P.groundSlope P.length * v P.length = 0 := by
  have hl : P.groundSlope 0 = -P.waveNumber * Real.sin (P.waveNumber * (0 - P.center)) := rfl
  have hr : P.groundSlope P.length =
      -P.waveNumber * Real.sin (P.waveNumber * (P.length - P.center)) := rfl
  rw [P.groundPhase_left] at hl
  rw [P.groundPhase_right] at hr
  cases he : P.ends <;> simp_all [zeroTraces]

theorem DirichletInterval.groundState_edgeEquation (P : DirichletInterval) :
    EdgeEquation (fun _ => 1) (fun x => P.waveNumber ^ 2 * P.groundState x)
      0 P.length P.groundState P.groundSlope := by
  refine ⟨(dirichletCosine_continuous _ _).continuousOn,
    (dirichletCosineSlope_continuous _ _).continuousOn, ?_, ?_⟩
  · intro x _
    change HasDerivAt (dirichletCosine P.waveNumber P.center)
      (dirichletCosineSlope P.waveNumber P.center x / 1) x
    simpa only [div_one] using dirichletCosine_hasDerivAt P.waveNumber P.center x
  · intro x _
    change HasDerivAt (dirichletCosineSlope P.waveNumber P.center)
      (-(P.waveNumber ^ 2 * dirichletCosine P.waveNumber P.center x)) x
    simpa only [neg_mul] using dirichletCosineSlope_hasDerivAt P.waveNumber P.center x

theorem DirichletInterval.groundState_weak (P : DirichletInterval) :
    DirichletWeakEigenEquation P (P.diffusivity * P.waveNumber ^ 2) P.groundState := by
  refine ⟨P.groundState_admissible, ?_⟩
  intro v hv
  have h := P.groundState_edgeEquation.green_identity_energy P.length_pos.le
    (continuousOn_const.mul (dirichletCosine_continuous _ _).continuousOn)
    (fun _ _ => one_ne_zero) hv.1
  have hb := P.groundSlope_boundary hv.2
  simp only [one_mul, hb.1, hb.2, add_zero, sub_zero] at h
  have he : (∫ x in (0 : ℝ)..P.length, P.waveNumber ^ 2 * P.groundState x * v x) =
      P.waveNumber ^ 2 * (∫ x in (0 : ℝ)..P.length, P.groundState x * v x) := by
    simp only [mul_assoc, intervalIntegral.integral_const_mul]
  rw [he] at h
  rw [h]
  ring

end TimeTraps.Spectral
