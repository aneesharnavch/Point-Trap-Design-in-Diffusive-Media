module

public import TimeTraps.Probability.ReversibleNeumannMartingaleProblemRestartData

@[expose] public section

/-! The original test martingale supplies the Dynkin identity after
any deterministic restart, tested against every event in the information
available then. No conditional transition law is assumed. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {A : IntervalMedium}
variable {X : ℝ≥0 → Ω → ℝ} {G : Filtration ℝ≥0 mΩ} {μ : Measure Ω} [IsProbabilityMeasure μ] {x : ℝ}

theorem ReversibleNeumannMartingaleProblem.restart_test_mean
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ReversibleNeumannTest A)
    (s t : ℝ≥0) {E : Set Ω} (hE : MeasurableSet[G s] E) :
    (∫ ω in E, H.value (X (s + t) ω) - H.value (X s ω) -
      (∫ r in (0 : ℝ)..t.val, H.generator (X (s + r.toNNReal) ω)) ∂μ) = 0 := by
  have he := (h.test_martingale H).setIntegral_eq (le_add_of_nonneg_right (show (0 : ℝ≥0) ≤ t from zero_le)) hE
  have hi0 := ((h.test_martingale H).integrable s).restrict (s := E)
  have hi1 := ((h.test_martingale H).integrable (s + t)).restrict (s := E)
  calc
    _ = ∫ ω in E, reversibleNeumannTestProcess H X x (s + t) ω -
        reversibleNeumannTestProcess H X x s ω ∂μ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro ω
      have hs := nonnegativeTime_integral_shift (h.observation_continuous H.generator_continuous ω) s t
      change H.value (X (s + t) ω) - H.value (X s ω) -
          (∫ r in (0 : ℝ)..t.val, H.generator (X (s + r.toNNReal) ω)) =
        (H.value (X (s + t) ω) - H.value x -
          (∫ r in (0 : ℝ)..(s + t).val, H.generator (X r.toNNReal ω))) -
        (H.value (X s ω) - H.value x -
          (∫ r in (0 : ℝ)..s.val, H.generator (X r.toNNReal ω)))
      rw [hs]
      ring
    _ = (∫ ω in E, reversibleNeumannTestProcess H X x (s + t) ω ∂μ) -
        ∫ ω in E, reversibleNeumannTestProcess H X x s ω ∂μ := integral_sub hi1 hi0
    _ = 0 := sub_eq_zero.mpr he.symm

theorem ReversibleNeumannMartingaleProblem.restart_expected_dynkin
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ReversibleNeumannTest A)
    (s t : ℝ≥0) {E : Set Ω} (hE : MeasurableSet[G s] E) :
    (∫ ω in E, H.value (X (s + t) ω) ∂μ) =
      (∫ ω in E, H.value (X s ω) ∂μ) +
        ∫ r in (0 : ℝ)..t.val, ∫ ω in E, H.generator (X (s + r.toNNReal) ω) ∂μ := by
  have hi0 := (h.observation_integrable H.value_continuous s).restrict (s := E)
  have hi1 := (h.observation_integrable H.value_continuous (s + t)).restrict (s := E)
  have hti := h.restart_observation_timeIntegral_integrable H.generator_continuous E s t
  have he := h.restart_test_mean H s t hE
  have hexp : (∫ ω in E, H.value (X (s + t) ω) - H.value (X s ω) -
      (∫ r in (0 : ℝ)..t.val, H.generator (X (s + r.toNNReal) ω)) ∂μ) =
      (∫ ω in E, H.value (X (s + t) ω) ∂μ) - (∫ ω in E, H.value (X s ω) ∂μ) -
        (∫ ω in E, (∫ r in (0 : ℝ)..t.val, H.generator (X (s + r.toNNReal) ω)) ∂μ) :=
    (integral_sub (hi1.sub hi0) hti).trans
      (congrArg (fun z : ℝ => z -
        (∫ ω in E, (∫ r in (0 : ℝ)..t.val, H.generator (X (s + r.toNNReal) ω)) ∂μ))
          (integral_sub hi1 hi0))
  have hz := hexp.symm.trans he
  have hm := h.restart_observation_timeIntegral_mean H.generator_continuous E s t
  linarith

theorem ReversibleNeumannMartingaleProblem.restart_expected_dynkin_real
    (h : ReversibleNeumannMartingaleProblem A X G μ x) (H : ReversibleNeumannTest A)
    (s : ℝ≥0) {t : ℝ} (ht : 0 ≤ t) {E : Set Ω} (hE : MeasurableSet[G s] E) :
    (∫ ω in E, H.value (X (s + t.toNNReal) ω) ∂μ) =
      (∫ ω in E, H.value (X s ω) ∂μ) +
        ∫ r in (0 : ℝ)..t, ∫ ω in E, H.generator (X (s + r.toNNReal) ω) ∂μ := by
  have he := h.restart_expected_dynkin H s t.toNNReal hE
  exact he.trans (congrArg (fun r : ℝ => (∫ ω in E, H.value (X s ω) ∂μ) +
    ∫ z in (0 : ℝ)..r, ∫ ω in E, H.generator (X (s + z.toNNReal) ω) ∂μ) (Real.coe_toNNReal t ht))

end TimeTraps.Probability

end
