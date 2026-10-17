module

public import TimeTraps.Probability.BrownianSignIntegrandStochastic

@[expose] public section

/-! Positive-time Brownian evaluations have no atoms, by their actual
Gaussian law with positive variance. Fubini then excludes any fixed level
at almost every time/sample pair in the finite positive-time window. -/

namespace TimeTraps.Probability

open MeasureTheory ProbabilityTheory Set Filter
open scoped NNReal ENNReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {B : ℝ≥0 → Ω → ℝ} {P : Measure Ω}

theorem brownian_eval_level_measure_zero (hB : IsPreBrownianReal B P)
    {t : ℝ≥0} (ht : 0 < t) (a : ℝ) : P {ω | B t ω = a} = 0 := by
  have : NullSingletonClass (gaussianReal 0 t) := nullSingletonClass_gaussianReal (ne_of_gt ht)
  have h := (hB.hasLaw_eval t).measure_eq (p := fun x => x = a)
    (by simp)
  simpa using h

theorem brownian_eval_ne_level_ae (hB : IsPreBrownianReal B P)
    {t : ℝ≥0} (ht : 0 < t) (a : ℝ) : ∀ᵐ ω ∂P, B t ω ≠ a := by
  simpa only [ae_iff, not_not] using brownian_eval_level_measure_zero hB ht a

theorem brownian_positive_time_ne_level_prod_ae (hB : IsPreBrownianReal B P)
    (hjoint : Measurable (fun p : ℝ≥0 × Ω => B p.1 p.2)) (a : ℝ) (T : ℝ≥0) :
    ∀ᵐ p ∂(volume : Measure ℝ).prod P, p.1 ∈ Ioc (0 : ℝ) T.val → B p.1.toNNReal p.2 ≠ a := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hb : Measurable (fun p : ℝ × Ω => B p.1.toNNReal p.2) :=
    hjoint.comp ((by fun_prop : Measurable (fun p : ℝ × Ω => p.1.toNNReal)).prodMk measurable_snd)
  have hm : MeasurableSet {p : ℝ × Ω | p.1 ∈ Ioc (0 : ℝ) T.val → B p.1.toNNReal p.2 ≠ a} :=
    (measurableSet_Ioc.preimage measurable_fst).imp (measurableSet_eq_fun hb measurable_const).compl
  apply (Measure.ae_prod_iff_ae_ae hm).mpr
  filter_upwards [] with s
  by_cases hs : s ∈ Ioc (0 : ℝ) T.val
  · filter_upwards [brownian_eval_ne_level_ae hB (Real.toNNReal_pos.mpr hs.1) a] with ω hω
    exact fun _ => hω
  · exact Eventually.of_forall (fun _ h => False.elim (hs h))

end TimeTraps.Probability
