module

public import TimeTraps.Analysis.GraphHeatPointResolventRegularity
public import TimeTraps.Analysis.GraphHeatResolventContinuous
public import TimeTraps.Analysis.GraphHeatPointPotentialRevuz

@[expose] public section

/-! Absolute time/source integrability identifies the literal discounted
point potential by every continuous source test. -/

namespace TimeTraps.Analysis

open Set MeasureTheory TimeTraps.Graph Filter TimeTraps.Probability

variable {V E : Type*} [Fintype V] [Fintype E] [Nonempty E]

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_source_integrable
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (f : C(GraphRealization P.geometry, ℝ)) {q : ℝ} (hq : 0 < q) :
    Integrable (fun z : ℝ × GraphRealization P.geometry =>
      Real.exp (-(q * z.1)) * (f z.2 * P.realizedHeatPointPotential z.2 a z.1))
      ((volume.restrict (Ioi 0)).prod P.geometry.lengthMeasure) := by
  obtain ⟨C, _, hb⟩ := P.realizedHeatPointPotential_global_bound
  have hf : Integrable f P.geometry.lengthMeasure :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi := ((graphPointDiscount_envelope_integrable hq).const_mul C).mul_prod hf.norm
  have hparam : Continuous (fun z : ℝ × GraphRealization P.geometry => ((z.2, a), z.1)) :=
    (continuous_snd.prodMk continuous_const).prodMk continuous_fst
  have hU := P.realizedHeatPointPotential_joint_continuous.comp hparam
  have hexp : Continuous (fun z : ℝ × GraphRealization P.geometry => Real.exp (-(q * z.1))) := by fun_prop
  have hm := hexp.mul ((f.continuous.comp continuous_snd).mul hU)
  apply hi.mono' hm.aestronglyMeasurable
  have htime : ∀ᵐ z ∂((volume.restrict (Ioi (0 : ℝ))).prod P.geometry.lengthMeasure), 0 < z.1 :=
    (Measure.quasiMeasurePreserving_fst (μ := volume.restrict (Ioi (0 : ℝ)))
      (ν := P.geometry.lengthMeasure)).ae (ae_restrict_mem measurableSet_Ioi)
  filter_upwards [htime] with z hz
  change ‖Real.exp (-(q * z.1)) * (f z.2 * P.realizedHeatPointPotential z.2 a z.1)‖ ≤
    (C * (Real.exp (-(q * z.1)) * (z.1 + 2 * Real.sqrt z.1))) * ‖f z.2‖
  rw [norm_mul, Real.norm_eq_abs (Real.exp _), abs_of_pos (Real.exp_pos _), norm_mul,
    Real.norm_eq_abs (P.realizedHeatPointPotential _ _ _), abs_of_nonneg (hb z.1 hz.le z.2 a).2.1]
  have hh := mul_le_mul_of_nonneg_left (hb z.1 hz.le z.2 a).2.2
    (mul_nonneg (Real.exp_pos (-(q * z.1))).le (norm_nonneg (f z.2)))
  nlinarith

theorem GraphShiftedContactOperatorProblem.pointLocalTimeDiscountedPotential_one_pairing
    (P : GraphShiftedContactOperatorProblem V E) (a : GraphRealization P.geometry)
    (f : C(GraphRealization P.geometry, ℝ)) :
    (∫ x, f x * P.pointLocalTimeDiscountedPotential a 1 x ∂P.geometry.lengthMeasure) =
      P.realizedSolutionL (graphConservativeContinuousStateL P.geometry f) a := by
  have hi := P.pointLocalTimeDiscountedPotential_source_integrable a f (q := 1) (by norm_num)
  calc
    _ = ∫ x, (∫ H in Ioi (0 : ℝ),
        Real.exp (-(1 * H)) * (f x * P.realizedHeatPointPotential x a H)) ∂P.geometry.lengthMeasure := by
      apply integral_congr_ae
      apply Eventually.of_forall
      intro x
      simp only [pointLocalTimeDiscountedPotential, one_mul]
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Eventually.of_forall (fun H => by dsimp only; ring)
    _ = ∫ H in Ioi (0 : ℝ), ∫ x,
        Real.exp (-(1 * H)) * (f x * P.realizedHeatPointPotential x a H) ∂P.geometry.lengthMeasure :=
      (integral_integral_swap hi).symm
    _ = ∫ H in Ioi (0 : ℝ), Real.exp (-H) * P.occupationPotential f H a := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with H hH
      rw [integral_const_mul, P.realizedHeatPointPotential_source_pairing f a hH.le, one_mul]
    _ = _ := P.occupationPotentialLaplaceOne_apply f a

end TimeTraps.Analysis
