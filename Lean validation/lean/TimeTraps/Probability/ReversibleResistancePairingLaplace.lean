module

public import TimeTraps.Probability.ReversibleResistancePairingData

@[expose] public section

/-! Fubini for exponentially discounted physical initial-state pairings.
The resulting Laplace transform is the actual original Neumann resolvent;
no invariance or symmetry is used in this identification. -/

noncomputable section

namespace TimeTraps.Probability

open Set MeasureTheory ProbabilityTheory Filter TimeTraps.Interval
open scoped NNReal ENNReal Topology BoundedContinuousFunction

theorem reversibleResistanceWeightedTransition_discounted_integrable (A : IntervalMedium)
    (w : C(Icc A.source.left A.source.right, ℝ)) (g : ℝ →ᵇ ℝ)
    {α : ℝ} (hα : 0 < α) :
    Integrable (fun p : ℝ × Icc A.source.left A.source.right =>
      Real.exp (-α * p.1) * (w p.2 * reversibleResistanceTransition A p.1.toNNReal g p.2.val))
      ((volume.restrict (Ioi (0 : ℝ))).prod (reversibleResistanceLengthMeasure A)) := by
  let q : ℝ × Icc A.source.left A.source.right → ℝ≥0 × Icc A.source.left A.source.right :=
    fun p => (p.1.toNNReal, p.2)
  have hq : Measurable q := (measurable_real_toNNReal.comp measurable_fst).prodMk measurable_snd
  have hm0 := (reversibleResistanceTransition_jointlyMeasurable_interval A g.continuous).comp hq
  have he : (fun p : ℝ × Icc A.source.left A.source.right =>
      reversibleResistanceTransition A p.1.toNNReal g p.2.val) =
      (fun p : ℝ≥0 × Icc A.source.left A.source.right =>
        reversibleResistanceTransition A p.1 g p.2.val) ∘ q := rfl
  have hm : Measurable (fun p : ℝ × Icc A.source.left A.source.right =>
      reversibleResistanceTransition A p.1.toNNReal g p.2.val) := he.symm ▸ hm0
  apply (((exp_neg_integrableOn_Ioi 0 hα).mul_const (‖w‖ * ‖g‖)).comp_fst
    (reversibleResistanceLengthMeasure A)).mono'
    (((by fun_prop : Measurable (fun p : ℝ × Icc A.source.left A.source.right =>
      Real.exp (-α * p.1))).mul ((w.continuous.measurable.comp measurable_snd).mul hm)).aestronglyMeasurable)
  apply Eventually.of_forall
  intro p
  change ‖Real.exp (-α * p.1) * (w p.2 * reversibleResistanceTransition A p.1.toNNReal g p.2.val)‖ ≤
    Real.exp (-α * p.1) * (‖w‖ * ‖g‖)
  rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  rw [norm_mul]
  exact mul_le_mul (w.norm_coe_le_norm p.2)
    (reversibleResistanceTransition_bound A p.1.toNNReal g.norm_coe_le_norm p.2.val)
    (norm_nonneg _) (norm_nonneg _)

theorem reversibleResistanceWeightedTransition_laplace (A : IntervalMedium)
    (w : C(Icc A.source.left A.source.right, ℝ)) (g : ℝ →ᵇ ℝ)
    (H : ReversibleNeumannTest A) {α : ℝ} (hα : 0 < α)
    (hH : ∀ x ∈ Icc A.source.left A.source.right, α * H.value x - H.generator x = g x) :
    (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) * reversibleResistanceWeightedTransition A w g t.toNNReal) =
      ∫ x, w x * H.value x.val ∂reversibleResistanceLengthMeasure A := by
  have hi := reversibleResistanceWeightedTransition_discounted_integrable A w g hα
  calc
    _ = ∫ t in Ioi (0 : ℝ), ∫ x,
        Real.exp (-α * t) * (w x * reversibleResistanceTransition A t.toNNReal g x.val)
          ∂reversibleResistanceLengthMeasure A := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun t => (integral_const_mul _ _).symm)
    _ = ∫ x, (∫ t in Ioi (0 : ℝ),
        Real.exp (-α * t) * (w x * reversibleResistanceTransition A t.toNNReal g x.val))
          ∂reversibleResistanceLengthMeasure A := integral_integral_swap hi
    _ = _ := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      have hlap : (∫ t in Ioi (0 : ℝ), Real.exp (-α * t) *
          reversibleResistanceTransition A t.toNNReal g x.val) = H.value x.val :=
        ReversibleNeumannMartingaleProblem.resolvent_laplace (Ω := BrownianCompletedSample)
          (X := fun t (ω : BrownianCompletedSample) => reversibleResistancePath A x.val t ω)
          (reversibleResistancePath_martingaleProblem A x.property) H hα hH
      calc
        _ = ∫ t in Ioi (0 : ℝ), w x * (Real.exp (-α * t) *
            reversibleResistanceTransition A t.toNNReal g x.val) := by
          apply integral_congr_ae
          exact Eventually.of_forall (fun t => by ring)
        _ = _ := by rw [integral_const_mul, hlap]

end TimeTraps.Probability

end
