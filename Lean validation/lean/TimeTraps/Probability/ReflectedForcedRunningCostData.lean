module

public import TimeTraps.Spectral.ReflectedForcedKinkOperator
public import TimeTraps.Probability.ReflectedAtomicWeightedValueTime

@[expose] public section

/-! Continuous signed physical sources are evaluated only on the closed
reflected range. Their canonical folded extensions establish actual
measurability and finite-time integrability without any assumption on
the source outside that range. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter TimeTraps.Analysis TimeTraps.Spectral
open scoped NNReal ENNReal Topology

variable {n : ℕ} {P : SpectralProblem n} {g : ℝ → ℝ}

theorem reflectedForcedRunningCost_extension
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) (T : ℝ≥0) (ω : ℕ → ℝ) :
    reflectedAtomicWeightedValue
      (reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg))
      P.length P.diffusivity x P.site P.strength T ω =
      reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength T ω := by
  unfold reflectedAtomicWeightedValue
  rw [forcedKinkSource_extension hg
    (foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath T ω)]

theorem reflectedForcedRunningCost_jointlyMeasurable
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) :
    Measurable (fun p : ℝ≥0 × (ℕ → ℝ) =>
      reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength p.1 p.2) := by
  have he : (fun p : ℝ≥0 × (ℕ → ℝ) => reflectedAtomicWeightedValue
      (reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg))
      P.length P.diffusivity x P.site P.strength p.1 p.2) =
      (fun p => reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength p.1 p.2) :=
    funext (fun p => reflectedForcedRunningCost_extension hg x p.1 p.2)
  rw [← he]
  exact reflectedAtomicWeightedValue_jointlyMeasurable
    (reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg)).continuous
    P.length P.diffusivity x P.site P.strength

theorem reflectedForcedRunningCost_memLp
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) (T : ℝ≥0) :
    MemLp (reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength T)
      2 brownianDyadicMeasure := by
  apply (reflectedAtomicWeightedValue_memLp
    (reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg)).continuous
    P.length P.length_pos P.diffusivity P.diffusivity_pos x P.site P.strength
    (fun i => (P.strength_pos i).le) T).ae_eq
  exact Eventually.of_forall (reflectedForcedRunningCost_extension hg x T)

theorem reflectedForcedRunningCost_time_joint_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) (T : ℝ≥0) :
    Integrable (fun p : ℝ × (ℕ → ℝ) =>
      reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength p.1.toNNReal p.2)
      ((volume.restrict (Ioc (0 : ℝ) T.val)).prod brownianDyadicMeasure) := by
  apply (reflectedAtomicWeightedValue_time_joint_integrable
    (reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg)).continuous
    P.length P.length_pos P.diffusivity P.diffusivity_pos x P.site P.strength
    (fun i => (P.strength_pos i).le) T).congr
  exact Eventually.of_forall (fun p => reflectedForcedRunningCost_extension hg x p.1.toNNReal p.2)

theorem reflectedForcedRunningCost_time_integral_integrable
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) (T : ℝ≥0) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..T.val,
      reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω)
      brownianDyadicMeasure := by
  apply (reflectedForcedRunningCost_time_joint_integrable hg x T).integral_prod_right.congr
  exact Eventually.of_forall (fun _ => (intervalIntegral.integral_of_le T.coe_nonneg).symm)

theorem reflectedForcedRunningCost_mean_time_integral
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, (∫ r in (0 : ℝ)..T.val,
      reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω)
      ∂brownianDyadicMeasure) =
      ∫ r in (0 : ℝ)..T.val,
        reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal := by
  calc
    _ = ∫ ω, (∫ r in Ioc (0 : ℝ) T.val,
        reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength r.toNNReal ω)
        ∂brownianDyadicMeasure := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun _ => intervalIntegral.integral_of_le T.coe_nonneg)
    _ = ∫ r in Ioc (0 : ℝ) T.val,
        reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength r.toNNReal :=
      (integral_integral_swap (reflectedForcedRunningCost_time_joint_integrable hg x T)).symm
    _ = _ := (intervalIntegral.integral_of_le T.coe_nonneg).symm

theorem reflectedForcedRunningCost_expectation_continuous
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) :
    Continuous (reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength) := by
  have he : reflectedAtomicValueExpectation
      (reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg))
      P.length P.diffusivity x P.site P.strength =
      reflectedAtomicValueExpectation g P.length P.diffusivity x P.site P.strength := by
    funext T
    exact integral_congr_ae (Eventually.of_forall (reflectedForcedRunningCost_extension hg x T))
  rw [← he]
  exact reflectedAtomicValueExpectation_continuous
    (reflectedFellerExtension P.length P.length_pos (forcedKinkSource P g hg)).continuous
    P.length P.length_pos P.diffusivity P.diffusivity_pos x P.site P.strength
    (fun i => (P.strength_pos i).le)

theorem reflectedForcedRunningCost_integral_norm_le
    (hg : ContinuousOn g (Icc 0 P.length)) (x : ℝ) (T : ℝ≥0) :
    (∫ ω, ‖reflectedAtomicWeightedValue g P.length P.diffusivity x P.site P.strength T ω‖
      ∂brownianDyadicMeasure) ≤
      ‖forcedKinkSource P g hg‖ *
        reflectedAtomicMeanSurvival P.length P.diffusivity x P.site P.strength T := by
  rw [reflectedAtomicMeanSurvival, ← integral_const_mul]
  apply integral_mono ((reflectedForcedRunningCost_memLp hg x T).integrable (by norm_num)).norm
    ((reflectedAtomicSurvival_integrable P.length P.diffusivity_pos x P.site P.strength
      (fun i => (P.strength_pos i).le) T).const_mul _)
  intro ω
  have hw := (reflectedAtomicSurvival_bounds P.length P.diffusivity_pos x P.site P.strength
    (fun i => (P.strength_pos i).le) T ω).1
  have hb := (forcedKinkSource P g hg).norm_coe_le_norm
    ⟨_, foldedTrajectory_mem P.length P.length_pos P.diffusivity x brownianDyadicPath T ω⟩
  change ‖g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω)‖ ≤ _ at hb
  change ‖reflectedAtomicSurvival P.length P.diffusivity x P.site P.strength T ω *
    g (foldedTrajectory P.length P.diffusivity x brownianDyadicPath T ω)‖ ≤
      ‖forcedKinkSource P g hg‖ * reflectedAtomicSurvival P.length P.diffusivity x P.site P.strength T ω
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos hw]
  exact (mul_le_mul_of_nonneg_left hb hw.le).trans_eq (mul_comm _ _)

end TimeTraps.Probability
