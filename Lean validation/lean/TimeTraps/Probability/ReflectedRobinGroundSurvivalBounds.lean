module

public import TimeTraps.Probability.ReflectedRobinEigenExpectation
public import TimeTraps.Spectral.RobinOperatorGround

@[expose] public section

/-! A positive physical ground state bounds the actual survival
probability by positive constant multiples of its exact eigenvalue
exponential. The compact minimum is strictly positive, including both
reflecting endpoints. These are bounds, not a second-eigenvalue remainder. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : RobinProblem n} {ev : ℝ}

theorem reflectedPositiveRobinEigenstate_survival_bounds (E : PositiveRobinEigenstate P ev) :
    ∃ m M : ℝ, 0 < m ∧ 0 < M ∧
      (∀ z ∈ Icc 0 P.length, m ≤ E.state z ∧ E.state z ≤ M) ∧
      ∀ x ∈ Icc 0 P.length, ∀ T : ℝ≥0,
        E.state x / M * Real.exp (-ev * T.val) ≤
          reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ∧
        reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ≤
          E.state x / m * Real.exp (-ev * T.val) := by
  have hc : ContinuousOn E.state (Icc 0 P.length) := by
    simpa only [uIcc_of_le P.length_pos.le] using E.energy.continuousOn
  have hn : (Icc (0 : ℝ) P.length).Nonempty := ⟨0, le_rfl, P.length_pos.le⟩
  obtain ⟨y, hy, hmin⟩ := isCompact_Icc.exists_isMinOn hn hc
  obtain ⟨z, hz, hmax⟩ := isCompact_Icc.exists_isMaxOn hn hc
  have hm := E.positive y hy
  have hM := E.positive z hz
  refine ⟨E.state y, E.state z, hm, hM, fun w hw => ⟨hmin hw, hmax hw⟩, ?_⟩
  intro x hx T
  have hW := reflectedAtomicSurvival_integrable P.length P.diffusivity_pos x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight)
    (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg) T
  have hV := (reflectedRobinRunningCost_memLp P.length P.length_pos P.diffusivity P.diffusivity_pos
    (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight)
    (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg) hc x T).integrable (by norm_num)
  have he := reflectedRobinWeakEigenstate_expectation_at_start E.to_weak hx T
  simp only [reflectedRobinSurvival_eq_atomic P.length P.diffusivity_pos] at he
  change reflectedAtomicValueExpectation E.state P.length P.diffusivity x
    (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T = _ at he
  have hl : E.state y * reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ≤
      reflectedAtomicValueExpectation E.state P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T := by
    rw [reflectedAtomicMeanSurvival, ← integral_const_mul]
    apply integral_mono (hW.const_mul _) hV
    intro ω
    have hp := (reflectedAtomicSurvival_bounds P.length P.diffusivity_pos x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight)
      (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg) T ω).1.le
    have hv := hmin (foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath T ω)
    change E.state y * reflectedAtomicSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ω ≤
      reflectedAtomicSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ω *
        E.state (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω)
    exact (mul_comm _ _).le.trans (mul_le_mul_of_nonneg_left hv hp)
  have hr : reflectedAtomicValueExpectation E.state P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ≤
      E.state z * reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T := by
    rw [reflectedAtomicMeanSurvival, ← integral_const_mul]
    apply integral_mono hV (hW.const_mul _)
    intro ω
    have hp := (reflectedAtomicSurvival_bounds P.length P.diffusivity_pos x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight)
      (reflectedRobinStrength_nonneg (fun i => (P.strength_pos i).le) P.betaLeft_nonneg P.betaRight_nonneg) T ω).1.le
    have hv := hmax (foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath T ω)
    change reflectedAtomicSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ω *
      E.state (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω) ≤
        E.state z * reflectedAtomicSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ω
    exact (mul_le_mul_of_nonneg_left hv hp).trans_eq (mul_comm _ _)
  constructor
  · calc
      _ = reflectedAtomicValueExpectation E.state P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T / E.state z := by
        rw [he]
        ring
      _ ≤ _ := (div_le_iff₀ hM).mpr (by nlinarith [hr])
  · calc
      _ ≤ reflectedAtomicValueExpectation E.state P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T / E.state y :=
        (le_div_iff₀ hm).mpr (by nlinarith [hl])
      _ = _ := by rw [he]; ring

theorem reflectedRobinPrincipal_survival_uniform_bounds (P : RobinProblem n) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ x ∈ Icc 0 P.length, ∀ T : ℝ≥0,
      c * Real.exp (-P.principalValue * T.val) ≤
        reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ∧
      reflectedAtomicMeanSurvival P.length P.diffusivity x (reflectedRobinSite P.length P.site) (reflectedRobinStrength P.strength P.betaLeft P.betaRight) T ≤
        C * Real.exp (-P.principalValue * T.val) := by
  obtain ⟨E, _⟩ := P.principal_eigenstate_exists
  obtain ⟨m, M, hm, hM, hbound, hs⟩ := reflectedPositiveRobinEigenstate_survival_bounds E
  refine ⟨m / M, M / m, div_pos hm hM, div_pos hM hm, ?_⟩
  intro x hx T
  have hp : 0 ≤ Real.exp (-P.principalValue * T.val) := (Real.exp_pos _).le
  exact ⟨(mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hbound x hx).1 hM.le) hp).trans
      (hs x hx T).1,
    (hs x hx T).2.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_right (hbound x hx).2 hm.le) hp)⟩

end TimeTraps.Probability
